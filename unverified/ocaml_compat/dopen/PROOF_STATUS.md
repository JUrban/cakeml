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
It also includes a deliberately malformed inference environment in which
only the value and type namespaces contain `M`; opening it must fail because
the constructor component is absent.  This pins the all-components selector
contract used by the alignment proof.

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
2. Inference-side success implies declarative-side selector success under
   `env_rel`, and matching selected results preserve `env_rel`, including
   nested module domains.
3. The generalized declaration/result soundness statement above, state/ID
   preservation for `Dopen`, and its declaration-list composition.
4. `cmlPtreeConversionProps$Decl_OK` branches for the two new grammar
   productions, followed by parser-to-inference constructor resolution,
   wrong-arity, and shadowing regressions.  The current parser has no active
   constructor-arity state to mutate; see `DESIGN.md`.
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

### Next lemma: selection preserves `env_rel`

There are two lemmas, in this order.  `infer_d` supplies only inference-side
success, so matching success cannot be assumed at the soundness call site:

```text
env_rel tenv ienv /\
open_ienv path ienv = SOME inferred_open
  ==> exists typed_open.
        open_tenv path tenv = SOME typed_open
```

Unfolding `open_ienv` gives successful value, constructor, and type namespace
selections.  For the value component, use the module-domain equivalence in
`env_rel` plus `nsOpen_some_from_same_mod_domain`; inference-side `SOME`
rules out declarative-side `NONE` at the same non-empty path.  For constructor
and type components, `env_rel_sound` gives exact namespace equality, so their
same-path selections are the identical `SOME` results.  The witness is the
record made from those three declarative selections.  Checking only the value
module domain would be insufficient: `open_tenv` succeeds only if all three
component selectors succeed.

The branch now contains this alignment statement as
`env_rel_open_tenv_exists`, backed by the generic namespace-domain lemma
`nsOpen_some_from_same_mod_domain`.  It remains an unbuilt proof candidate;
no downstream theorem currently depends on it.

Only after that alignment lemma should the preservation theorem assume the
two matching successful results:

```text
env_rel tenv ienv /\
open_tenv path tenv = SOME typed_open /\
open_ienv path ienv = SOME inferred_open
  ==> env_rel typed_open inferred_open
```

Its proof should unfold the record selectors only once and then transport the
five conjuncts of `env_rel` as follows.

1. `ienv_ok {}` and `tenv_ok` are component-wise `nsAll` properties.  Apply
   `nsAll_after_nsLookupMod`; their predicates ignore the qualified identifier,
   so the prefixed identifier produced by the lemma simplifies away.
2. Module-domain agreement for a suffix `q` follows by rewriting each lookup
   below the selected namespace to the original lookup at `path ++ q` with
   `nsLookupMod_after_nsLookupMod`, then instantiating the input domain
   agreement at that appended path.
3. The exact constructor and type components in `env_rel_sound` and
   `env_rel_complete` follow from their input equalities and selection at the
   same path.
4. For sound value lookup, turn a lookup in `inferred_open.inf_v` into the
   input lookup at
   `mk_id (path ++ id_to_mods id) (id_to_n id)` using
   `nsLookup_after_nsLookupMod`.  Apply input `env_rel_sound`; with `Empty`,
   `lookup_var` reduces to the declarative value namespace.  The same lookup
   lemma in reverse moves that result into `typed_open.v`.  The
   `tscheme_approx` witness is unchanged.
5. The complete direction is symmetric, starting from the selected
   declarative lookup and applying input `env_rel_complete`.

This lemma needs no `nsAppend` reasoning: opening is selection.  `nsAppend`
enters only in the declaration-list case, where the relational soundness
results for the head and tail compose via the existing `env_rel_extend`.

The branch now also contains the preservation statement as the unbuilt
`env_rel_open` proof candidate.  Its proof follows the five transports above,
with six separate `nsAll_after_nsOpen` uses for the inference/declarative
value, constructor, and type well-formedness components.  This is deliberately
not wired into `infer_d_sound` before the selector proof gate is green.

After the lemma is green, the mutual soundness result should return an
existential typed delta related to the inferred delta.  Existing declaration
cases can still choose `ienv_to_tenv inferred_delta`; Dopen chooses
`typed_open`.  A separate exact-input corollary can retain the convenient
syntactic result when `tenv = ienv_to_tenv ienv`, using
`ienv_to_tenv_open` and `ienv_to_tenv_extend`.  It cannot replace the
relational theorem because the current public soundness assumptions contain
only `env_rel`.

The unbuilt `dopenTests` theory now contains an inference-level arity witness:
an older top-level `C` takes one argument, the opened module's `C` takes zero,
and `[Dopen M; val y = C]` succeeds while `[Dopen M; val y = C 1]` fails.
This pins constructor shadowing through `inf_c`.  Two additional candidates
run the source strings `open M; val y = C` and `open M; val y = C 1` through
`lexer_fun`, `parse_prog`, and `infertype_prog`; they pin the same success and
wrong-arity failure end to end.  The `Decl_OK` proof candidate now has branches
for both the `StructName` and `LongidT` open productions.  None of these A2
claims is green until the parser-properties and `dopenTests` build gates pass.

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

## Build gates

The foundational gate is green against shared HOL commit
`a390cbabd3a4521bab4ee20281e3e42933a8a3ae`, using one worker.  The first run
failed in `cmlPtreeConversionTheory` on the new non-empty path theorem; after
unfolding `OPTION_CHOICE`/`OPTION_BIND` and using `APPEND_eq_NIL`, the rerun and
the remaining foundational theories completed:

```text
semantics/cmlPtreeConversionTheory.uo
semantics/semanticPrimitivesTheory.uo
semantics/evaluateTheory.uo
semantics/typeSystemTheory.uo
```

The shared HOL checkout is temporarily owned by another work lane after the
explicit foundational handoff.  Once it is released again, continue with one
worker and stop at the first honest failure (already-green targets are retained
below so the command sequence remains reproducible):

```sh
export HOLDIR=/project/worktrees/HOL-cakeml-dopen-v13
cd /project/worktrees/cakeml-dopen-v13/semantics
"$HOLDIR/bin/Holmake" -j 1 namespaceTheory.uo astTheory.uo \
  gramTheory.uo cmlPtreeConversionTheory.uo \
  semanticPrimitivesTheory.uo evaluateTheory.uo typeSystemTheory.uo

cd /project/worktrees/cakeml-dopen-v13/semantics/proofs
"$HOLDIR/bin/Holmake" -j 1 namespacePropsTheory.uo \
  cmlPtreeConversionPropsTheory.uo

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
