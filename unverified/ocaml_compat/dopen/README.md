# OCaml `open` oracle

This directory is the first A0 regression slice for the verified `Dopen`
work package in the Flyspeck/Candle compatibility program.  It records
observable OCaml behaviour before the CakeML AST or inference proofs are
changed.  It is deliberately an oracle, not an implementation of `Dopen` and
not evidence that CakeML accepts these programs yet.

The cases cover declaration-open precedence, repeated opens, later
declarations, values, constructors, type names, exceptions, nested module
paths, modules exposed by an open, qualified-name stability, module aliases,
and expression-level `let open`.  Failure cases pin missing top-level and
nested modules.  Each case is independent so a disagreement can be minimized
without loading the rest of the corpus.

The reference compiler is pinned to OCaml 4.14.1, matching the current
Flyspeck/HOL Light development environment.  Run the pack with:

```sh
./run-oracle.sh
./run-inventory-test.sh
```

The runner copies sources into a temporary directory, so it leaves no OCaml
build products in the checkout.  A different compiler version is rejected;
changing the pin is a compatibility decision and must be reviewed together
with regenerated expectations.

`let_open.ml` is included in the oracle inventory but does not decide whether
expression-level open belongs to the supported Candle subset.  The pinned
source-corpus inventory must make that scope decision; declaration open must
not silently acquire an unproved expression-open implementation.

`open_inventory.py` is a conservative lexical inventory tool for the real
HOL Light/Flyspeck sources.  A stock OCaml parser cannot read their HOL
quotations without the pinned preprocessor, so the tool ignores nested
comments, strings, single-line backtick quotations, and double-backtick
quotations and emits only unambiguous token prefixes.  Its output must still
be reviewed against the ordered production manifest; it is not a replacement
for parser acceptance tests.

Files ending in `.hl` use HOL mode, where single-backtick quotations may span
lines.  Plain `.ml`/`.mli` files use the conservative same-line rule so Camlp5
revised-syntax stream tokens are not mistaken for HOL quotations.

`scan_flyspeck_build.py` extracts the comment-aware ordered
`Build.build_sequence_full` list, requires an exact Flyspeck Git head, resolves
every entry, and reports either a stable summary or full TSV inventory.  For
roadmap v1.3's audited direct-source pin (kept separate from PFT-added source):

```sh
./scan_flyspeck_build.py \
  --flyspeck-root /project/worktrees/flyspeck-v13-source \
  --expected-head 1ce0353008eba83d3c76ae9a25c3c242e4802d53
```

The production loader has an earlier compatibility boundary that is not in
`Build.build_sequence_full`: `strictbuild.hl` begins with exact `#load`
directives for `unix.cma` and `str.cma`.  Freeze that separate, fail-closed
inventory with:

```sh
./scan_bootstrap_directives.py \
  --flyspeck-root /project/worktrees/flyspeck-v13-source \
  --expected-head 1ce0353008eba83d3c76ae9a25c3c242e4802d53
./test_bootstrap_directives.py
```

The scanner is not a normalizer and acceptance is not a claim that Candle
provides either library.  Any later removal of those two directives requires
an explicit contract showing that their required bindings are already in the
compiled environment.  Unknown or malformed directives must remain errors.
