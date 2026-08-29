# Candle parser diagnostic protocol migration

This CakeML branch implements the dedicated, parser-only Flyspeck diagnostic
around `caml_parser$run`.  It does not call the CakeML parser, the Candle REPL,
inference, evaluation, compilation, or source actions.

The capability request and response remain byte-for-byte unchanged:

```text
cake --candle-parser-diagnostic-capability-v1
CANDLE_CAMLPARSER_DIAGNOSTIC_CAPABILITY_V1\tcaml_parser$run\tstdin-exact-bytes\tparser-only\tno-inference\tno-evaluation\n
```

The capability form is the sole argument.  It does not open or read stdin,
returns status 0, emits the one line on stdout, and emits no stderr.

The run form also remains:

```text
cake --candle-parser-diagnostic-v1 NONCE
```

`NONCE` is exactly 64 lowercase hexadecimal characters.  Any other argument
list follows the ordinary compiler dispatch.  A run reads stdin exactly once
and passes exactly those characters to `caml_parser$run`.  Its only accepted
responses are now:

```text
CANDLE_CAMLPARSER_DIAGNOSTIC_V1\tNONCE\tOK\n
CANDLE_CAMLPARSER_DIAGNOSTIC_V1\tNONCE\tPARSE_ERROR\n
```

`OK` returns status 0 and empty stderr.  `PARSE_ERROR` writes
`ERR + "\nParsing failed at " + LOCATION` to stderr and terminates through
`Runtime.exit 65`.  The output record has no digest field.

## Required Candle controller migration

The existing controller draft expected a fourth, runtime-computed SHA-256
field on `PARSE_ERROR`.  Before linking or launching this runtime, update the
controller and regenerate its committed manifest/pilot artifacts as follows:

1. Require the parse-error stdout bytes to equal the three-field record above
   exactly.  Reject a trailing tab, digest, field, byte, or second line.
2. Continue requiring exit status exactly 65 and strictly well-formed UTF-8
   stderr.  Keep stdout and stderr in the current separate capped ordinary
   files owned by the fresh supervised process.
3. Compute
   `SHA256(ASCII("CANDLE_CAMLPARSER_ERROR_V1") || 0x00 || STDERR_BYTES)` in the
   controller after stable capture.  Store the lowercase digest in the attempt
   evidence as a controller-derived binding; do not describe it as a runtime
   assertion or parse proof.
4. Bump the evidence object's `parser_runtime_protocol.schema` from 1 to 2,
   while retaining the exact `-v1` command-line and wire identifiers above.
   This distinguishes already materialized schema-1 plans from the changed
   parse-error record without inventing a second runtime capability name.
5. Replace digest-field parser tests with tests that reject extra stdout data,
   validate the exact status-65/error record, and independently recompute the
   domain-separated digest from the captured stderr snapshot.

The controller-side digest is equally closed under the established execution
model: the nonce-bearing stdout and stderr are captured from the same fresh
process invocation, and the controller authenticates and hashes those stable
files.  A runtime-computed digest would duplicate that calculation without
adding evidence that `caml_parser$run` was called; that assurance comes from
the translated function and its HOL specification.

## Proof boundary

`compiler64ProgScript.sml` provides separate characteristic-formula,
whole-program, and source-semantics theorems for the capability, parse-success,
and parse-error modes.  The error theorem exposes the exact final FFI event
`ExtCall "exit" [] [65w] FFI_diverged`; the x64 bootstrap's linked
`basis_ffi.c` is the tracked symlink to `basis/basis_ffi.c`, whose `ffiexit`
passes that byte directly to C `exit`.  It does not use `cml_exit`, so the
optional nonzero-exit diagnostic in `cml_exit` does not append to this mode's
stderr.  The exact C source and link inputs remain part of linked provenance.

The existing theorem `semantics_compiler64_prog` intentionally excludes both
diagnostic modes, so its downstream `cake_compiled_thm` in
`x64BootstrapProofScript.sml` remains an ordinary-compiler theorem.  The three
new mode-specific source-semantics theorems are sufficient inputs for the same
generic `compile_correct_eval` composition used there: each supplies a
non-`Fail` singleton source behavior, while `compiler64_compiled` supplies the
compiled-program relation.  A verified-machine-code diagnostic claim still
requires replaying the x64 bootstrap proof with parallel mode-specific
instantiations of that composition (including the final-FFI outcome for exit
65).  Until those downstream theorems build, the present claim stops at the
source program's verified STDIO/COMMANDLINE/final-event semantics; it must not
be described as a verified property of a linked `cake` binary.

No parser pilot may run merely from this source change.  The new CakeML commit
must still be proof-built, pinned by the Candle manifest, bootstrapped, linked,
and accepted by the exact capability handshake under linked provenance.
