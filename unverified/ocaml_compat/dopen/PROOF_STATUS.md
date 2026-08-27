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

cd /project/worktrees/cakeml-dopen-v13/compiler/inference/proofs
"$HOLDIR/bin/Holmake" -j 1 envRelTheory.uo inferSoundTheory.uo \
  inferCompleteTheory.uo type_dCanonTheory.uo
```

After those targets are repaired, the acceptance build must include the
alternate semantics, source-to-flat/CV translator, bootstrap, and compiled
open-dependent regression.  Passing only the parser or `inferTheory` is not
the A3/A4 gate.
