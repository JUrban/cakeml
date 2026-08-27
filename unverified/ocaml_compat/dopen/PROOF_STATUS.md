# Declaration-open proof status

Date: 2026-08-27

This file is a deliberately explicit boundary around the first core code
slice.  It must not be read as a green proof/build report.

## Implemented equations

The current branch introduces:

- non-empty, path-based `namespace$nsOpen`;
- `Dopen locs (modN list)` plus syntax/pretty-print/S-expression support;
- grammar and parse-tree conversion for `open A` and `open A.B.C`, with a
  non-empty-path theorem and parser regressions;
- declaration-delta selectors for dynamic, declarative typing, inference,
  and source-to-flat environments;
- functional, big-step, small-step, itree, and translator evaluator cases;
- `type_d` and `infer_d` cases, including explicit located failure;
- a theorem that successful `infer_open` preserves the complete inference
  state; and
- source-to-flat and its CV-side equation, which emit no runtime declaration.

The executable test theory also fixes the sequencing contract at namespace
lookup level: an opened `x` shadows an older `x`, while a later declaration
delta shadows the opened `x`.  These tests exercise the existing
left-biased `extend_dec_env`; they do not replace its proof obligations.

Every successful layer returns the selected module contents only.  Existing
list sequencing appends that delta to the current environment exactly once.

## Soundness theorem obstruction

The obvious inference proof is not valid under the current theorem statement.
`infer_d_sound` concludes:

```text
type_d T tenv d ids (ienv_to_tenv inferred_delta)
```

For declarations that create fresh bindings, the proof chooses a declarative
derivation whose delta is exactly that conversion.  Open is different: it
exposes bindings already related by the input `env_rel tenv ienv`.

`env_rel` makes constructor and type namespaces equal, but its value
namespaces are related through sound and complete `tscheme_approx`; it does
not imply `tenv = ienv_to_tenv ienv`.  Therefore:

```text
open_ienv path ienv = SOME inferred_delta
```

does not justify the equality needed by the current `type_d` result, even when
the corresponding `open_tenv path tenv` succeeds.  Historical `dopen2` never
reached this proof and consequently does not answer the issue.

The leading repair candidate is to strengthen the declaration-level
soundness result to the relational statement actually needed for exposure:

```text
infer_d ... = success inferred_delta
  ==> exists typed_delta.
        type_d ... typed_delta /\ env_rel typed_delta inferred_delta
```

The list case then composes with the existing `env_rel_extend`.  Existing
fresh-binding cases can continue to choose `ienv_to_tenv inferred_delta` via
`env_rel_ienv_to_tenv`; the open case chooses the selected declarative delta
and needs a new module-selection preservation lemma.  Before adopting this
change, its downstream sufficiency for the final program soundness theorem
must be checked.  The alternative is a declarative equivalence relation on
opened value schemes, but that would duplicate the inference/type relation
inside `typeSystem` and currently has less evidence behind it.

The downstream check is now explicit.  The compiler-facing
`infertype_prog_correct` theorem only needs the existential result in
`can_type_prog`; it does not require the declarative delta to be syntactically
`ienv_to_tenv inferred_delta`.  The current internal `infer_top_sound` and
`infer_prog_sound` theorems do state that exact result, however, and are used
to compose successive top-level inference calls.  A relational repair must
therefore generalise those two results (and use `env_rel_extend` at each
composition point), or supply a separate exact-input corollary under
`tenv = ienv_to_tenv ienv`.  Merely changing the statement of `infer_d_sound`
would leave the proof stack incomplete.

Strengthening `env_rel` globally to equality is not a justified shortcut.
Its value component deliberately relates schemes through bidirectional
`tscheme_approx`; constructor and type namespaces are exact, but value
schemes need not be syntactically identical.  Conversely, changing `type_d`
to accept an arbitrary converted inference environment would leak inference
representation into the declarative semantics.  The module-selection
preservation lemma plus relational soundness remains the smallest candidate
that respects the existing abstraction boundary.

A concrete witness rules out treating this as a tactic accident.  Put one
closed integer binding under module `M`, with declarative scheme `(1,Tint)`
and inference scheme `(0,Infer_Tapp [] Tint_num)`, and use empty constructor
and type namespaces.  The unused declarative quantifier makes the schemes
syntactically different, while each is an instance of the other in the sense
used by the two `tscheme_approx` directions of `env_rel`.  Both environments
are well formed and have the same module domain.  Opening `M` therefore
preserves `env_rel` but cannot make the declarative result equal to
`ienv_to_tenv` of the inference result.

No equality axiom, `cheat`, qualification rewrite, or host-inference bypass is
present or proposed.

## Required lemmas and repairs

The next proof pass must establish, in order:

1. `nsOpen` lookup, `nsMap`, `nsAppend`, and module-domain lemmas for non-empty
   paths (the elementary lookup and `nsMap` lemmas are already in the slice).
2. Selection preserves `env_rel`: matching successful `open_tenv` and
   `open_ienv` results are related, including nested module domains.
3. The generalized declaration/result soundness statement above, state/ID
   preservation for `Dopen`, and its declaration-list composition.
4. `cmlPtreeConversionProps$Decl_OK` branches for the two new grammar
   productions and constructor-arity state work required by roadmap A2.
5. Type-system properties: weakening, lookup precedence, well-formedness,
   type-identity preservation, and `type_d` canonicalisation.
6. Inference completeness and CV correctness, including generated precondition
   and bootstrap-translation regeneration.
7. Functional/big-step/small-step/itree equivalence cases and source-to-flat
   correctness for the compile-time-only environment change.
8. Exhaustive AST consumers (presentation, S-expression round trip,
   translators, Candle safety predicates, REPL/eval support) identified by a
   clean full dependency build; generic wildcard consumers still need review,
   not just compilation.

## Static consumer backlog

Before any dependency build, an AST-constructor inventory found the following
files with declaration-specific branches but no `Dopen` occurrence.  This is
not evidence that every file needs a new semantic case: several proofs may
close a read-only, state-preserving case by simplification.  It is the exact
manual-review backlog, so a successful narrow parser build cannot hide it.

- evaluation/type-safety proof consumers:
  `semantics/proofs/typeSoundScript.sml`,
  `semantics/alt_semantics/proofs/interpScript.sml`,
  `compiler/repl/evaluate_initScript.sml`,
  `compiler/repl/evaluate_skipScript.sml`, and
  `candle/prover/candle_prover_evaluateScript.sml`;
- backend correctness consumers:
  `compiler/backend/proofs/source_evalProofScript.sml` and
  `compiler/backend/proofs/source_to_flatProofScript.sml`;
- inference proof consumers:
  `compiler/inference/proofs/inferSoundScript.sml` (known semantic
  obstruction), `compiler/inference/proofs/inferCompleteScript.sml`, and
  `compiler/inference/proofs/type_dCanonScript.sml`;
- translator/REPL consumers:
  `translator/ml_progLib.sml` and
  `compiler/repl/repl_init_envProgScript.sml`.  The core translator theorem
  file now has a `Decls_Dopen` equation, but that theorem is still in the
  deferred HOL build set.

Additional files that branch on `Dmod`/`Dlocal` but may use generic cases are
`semantics/alt_semantics/proofs/bigSmallEquivScript.sml`,
`semantics/alt_semantics/proofs/itree_semanticsEquivScript.sml`,
`semantics/alt_semantics/proofs/smallStepPropsScript.sml`,
`compiler/backend/source_letScript.sml`,
`compiler/backend/proofs/source_letProofScript.sml`,
`compiler/inference/inferPropsScript.sml`,
`compiler/bootstrap/translation/inferProgScript.sml`,
`compiler/parsing/ocaml/camlPtreeConversionScript.sml`, and the Candle
AST/presentation helpers under `candle/`.  A full reverse-dependency build is
still the authority on completeness.

## Deferred build commands

The shared HOL checkout is temporarily owned by another work lane.  No
`Holmake` command was run for this code slice while it was shared.  Once it is
released, start with one worker and stop at the first honest failure:

```sh
export HOLDIR=/project/worktrees/HOL-cakeml-dopen-v13
cd /project/worktrees/cakeml-dopen-v13/semantics
"$HOLDIR/bin/Holmake" -j 1 namespaceTheory.uo astTheory.uo \
  gramTheory.uo cmlPtreeConversionTheory.uo \
  semanticPrimitivesTheory.uo evaluateTheory.uo typeSystemTheory.uo

cd /project/worktrees/cakeml-dopen-v13/semantics/proofs
"$HOLDIR/bin/Holmake" -j 1 namespacePropsTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/parsing/tests
"$HOLDIR/bin/Holmake" -j 1 cmlTestsTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/inference
"$HOLDIR/bin/Holmake" -j 1 inferTheory.uo infer_cvTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/inference/tests
"$HOLDIR/bin/Holmake" -j 1 dopenTestsTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/inference/proofs
"$HOLDIR/bin/Holmake" -j 1 envRelTheory.uo inferSoundTheory.uo \
  inferCompleteTheory.uo type_dCanonTheory.uo

cd /project/worktrees/cakeml-dopen-v13/translator
"$HOLDIR/bin/Holmake" -j 1 evaluate_decTheory.uo ml_progTheory.uo
```

After those targets are repaired, the acceptance build must include the
alternate semantics, source-to-flat/CV translator, bootstrap, and compiled
open-dependent regression.  Passing only the parser or `inferTheory` is not
the A3/A4 gate.
