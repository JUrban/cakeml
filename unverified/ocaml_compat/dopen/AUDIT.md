# Dopen v1.3 integration audit

Date: 2026-08-27

This audit fixes the integration boundary for roadmap v1.3 Work Package A.
It is intentionally narrower than a completion claim: the checked-in oracle
and inventory advance A0, and a path-based core candidate advances the
implementation surface, while A1--A4 proof and integration gates remain open.

## Pinned heads and ancestry

| Item | Commit | Role |
| --- | --- | --- |
| CakeML `master` / chosen integration base | `dcc03f2866f05b1db18b9f45c731ce45c3a3133e` | Current public master at audit time |
| CakeML `dopen` | `947cd55ce284658eadaa42a43c3ab0482057d269` | Original 2022 Open/Dopen branch tip |
| CakeML `dopen2` | `db69b70e9ee28abd5d144e210a8fc6a396be4454` | Historical experimental anchor |
| `master`--`dopen2` merge base | `5204d423c1b89d92a970f41f52da476d6cfb1e47` | CakeML master merged into `dopen2` on 2025-09-06 |
| Current HOL prerequisite | `a390cbabd3a4521bab4ee20281e3e42933a8a3ae` | Isolated HOL master built for current CakeML testing |
| OCaml oracle | `4.14.1` | Reference compiler for A0 cases |
| Flyspeck direct-source corpus | `1ce0353008eba83d3c76ae9a25c3c242e4802d53` | Roadmap v1.3 source inventory pin; excludes PFT-added source |

Enumerating local and remote refs found the two historical Dopen refs above
(in addition to this development branch).  `git ls-remote` confirmed both
public branch tips.  The current histories have 2,630 commits reachable only
from master and 13 reachable only from `dopen2`.  Twelve of those branch
commits are the 2022 Open/Dopen experiment ending at `dopen`; the thirteenth
is the 2025 master merge that produced `dopen2`.

Relative to the merge base, the Dopen-specific patch changes only these eight
files (657 insertions, 233 deletions):

```text
semantics/alt_semantics/bigStepScript.sml
semantics/astScript.sml
semantics/evaluateScript.sml
semantics/proofs/namespacePropsScript.sml
semantics/proofs/typeSysPropsScript.sml
semantics/proofs/weakeningScript.sml
semantics/semanticPrimitivesScript.sml
semantics/typeSystemScript.sml
```

It is therefore evidence and lemma material, not a branch that can satisfy
v1.3's verified-inference gate as-is.

## What `dopen2` contains

The branch adds expression `Open modN exp` and declaration `Dopen modN`, a
left-biased runtime `open_mod`, functional and relational evaluation clauses,
`tenvOpen`, declarative typing clauses, three namespace lookup/subenvironment
lemmas, and repairs in type-system/weakening theories.

The following acceptance layers have no Dopen change on that branch:

| Layer | `dopen2` status |
| --- | --- |
| Grammar and parse-tree conversion | Missing |
| AST printers/serializers/visitors | Missing |
| Parser constructor-arity and namespace state | Missing |
| Nested module paths | Missing (`modN`, not a path) |
| `infer_open` and `infer_e`/`infer_d` cases | Missing |
| Inference state/ID/stamp invariant | Missing |
| Inference soundness and `infer_d_check` stack | Missing |
| Inference canonicalization and completeness | Missing |
| CV inference translation and correctness | Missing |
| Bootstrap translation / compiled inferencer | Missing |
| OCaml differential or CakeML regressions | Missing |
| Compiled open-dependent Candle slice | Missing |

There is also a semantic interface question that must be resolved before a
port.  `tenvOpen` returns the selected module contents as an exposure delta,
and the declarative `Dopen` rule returns that delta.  In contrast, runtime
`open_mod` returns `nsAppend` of the selected contents and the entire current
environment, and the `Dopen` evaluator returns that combined environment as
its declaration result.  Sequencing declarations can consequently re-export
and duplicate pre-existing bindings.  This may be repairable, but the branch
does not prove that the dynamic result, declarative delta, and future
inferencer result implement one shared operation.  The v1.3 design should
make the delta/combined distinction explicit and prove it.

Applying the eight-file patch to current master is not mechanical.  A
three-way-free `git apply --check` fails in `semantics/astScript.sml`,
`semantics/semanticPrimitivesScript.sml`, and
`semantics/proofs/weakeningScript.sml`; the surrounding AST, primitive, and
proof APIs have changed.  Importing only the hunks that still apply would
recreate the exact proof-stack hole that the roadmap forbids.

## A0 corpus result

The conservative scanner was run over the current
`Build.build_sequence_full` list.  Its 297 ordered entries resolve to 287
unique paths (ten intentional repeated loads), with no missing file and no
scanner error.  It found:

| Construct | Occurrences |
| --- | ---: |
| Declaration `open` | 3,276 |
| Warning-suppressing `open!` | 0 |
| `include` | 1 |
| Module alias | 1 |
| Functor-definition prefix | 0 |
| First-class module prefix | 0 |
| Nested-path declaration `open` | 0 |
| Expression `let open` | 0 |

The inventory was rerun against exact direct-source commit `1ce0353...` after
a provenance review distinguished it from the later `2ea440e...` PFT-added
tree.  The selected build-manifest counts are unchanged, but only the direct
pin is authoritative for S2/S3 source-compatibility claims.

The one alias is `Set.Make` in `general/serialization.hl`; the one include is
`Flyspeck_eval` in `general/flyspeck_lib.hl`.  These are lexical inventory
results, not parser-acceptance results.  They show that declaration open is
high-frequency and belongs on the critical path.  They also justify deferring
expression `Open` from the first real Flyspeck slice unless the separately
pinned HOL Light/Candle base manifest demonstrates a dependency.  The oracle
keeps nested and expression-open cases visible so a later scope expansion
cannot silently choose semantics.

The first Dopen subset is consequently frozen as a declaration followed by a
non-empty module path.  Simple paths are required by the pinned Flyspeck
manifest; nested paths are supported and tested because the representation
cost is small and path resolution is already the namespace primitive.
Expression `let open`, `open!`, `include`, module aliases, functor syntax, and
first-class modules are not mapped to `Dopen`.  The manifest's single include
and functor-application alias remain separate compatibility-ledger blockers;
they must not be counted as solved by declaration open.

## First executable A0 slice

The first committed slice was a pinned OCaml 4.14.1 differential oracle.  Ten
independent cases cover:

- value precedence, repeated opens, later declarations, and qualified-name
  stability;
- constructors, type names, exceptions, and opened module namespaces;
- nested paths and module aliases;
- expression `let open` as an explicitly uncommitted scope case; and
- missing top-level and nested modules as negative cases.

The runner requires the exact compiler version, copies sources to a temporary
directory, compares exact stdout or diagnostic categories, and leaves no
compiler output in the checkout.  The separate lexical scanner has a fixture
covering comments, strings, HOL quotations, Camlp5 token syntax, `open!`,
aliases, functors, include, and first-class modules.

## Current core candidate

The branch now also contains a reviewable declaration-open vertical slice:
`Dopen locs (modN list)`, non-empty shared namespace selection, simple and
nested grammar/conversion tests, delta-only functional and relational
semantics, declarative typing, inference with unchanged state, CV hooks,
serialization/presentation, and compile-time source-to-flat exposure.

This code is deliberately not presented as proof-green.  The exact active
obstruction and the proposed relational repair are recorded in
[`PROOF_STATUS.md`](PROOF_STATUS.md).  In brief, the existing
`infer_d_sound` theorem demands exact equality between its declarative result
and `ienv_to_tenv` of its inference result.  Opening exposes an existing input
environment whose value schemes are related by `env_rel`/`tscheme_approx`, not
necessarily syntactically equal.  The proof must be generalized or supplied
with a justified declarative equivalence; no assumption or inference bypass
has been inserted.

### Current-base parser-state finding

The roadmap's constructor-arity parser-state requirement does not map
literally to the chosen CakeML base.  A repository-wide reference audit shows
that `PCstate0.ctr_arities` is only declared and initialized; no parser entry
point reads or updates it, and the parser tests state that the former
`elab_decs` phase no longer exists.  Current conversion recognizes constructor
names syntactically and builds constructor/pattern applications directly;
arity validation belongs to inference.  The Dopen A2 gate on this base is
therefore constructor lookup through the selected `inf_c` namespace, including
correct-arity, wrong-arity, and shadowing tests, together with the missing
`Decl_OK` grammar proof.  Reintroducing unused parser state would add an
unverified second namespace mechanism and is not proposed.

## Commands and current evidence

Run the committed A0 lane:

```sh
cd /project/worktrees/cakeml-dopen-v13
./unverified/ocaml_compat/dopen/run-oracle.sh
./unverified/ocaml_compat/dopen/run-inventory-test.sh
./unverified/ocaml_compat/dopen/scan_flyspeck_build.py \
  --flyspeck-root /project/worktrees/flyspeck-v13-source \
  --expected-head 1ce0353008eba83d3c76ae9a25c3c242e4802d53
```

Expected terminal markers are:

```text
OCAML_OPEN_ORACLE_OK cases=10 version=4.14.1
OCAML_OPEN_INVENTORY_TEST_OK
FLYSPECK_OPEN_INVENTORY_OK
```

The isolated HOL prerequisite was configured and completed without its
optional help documentation, using one requested build worker:

```sh
cd /project/worktrees/HOL-cakeml-dopen-v13
poly --script tools/smart-configure.sml
bin/build -j 1 --no-helpdocs
bin/Holmake --help
bin/hol heapname
```

The build ended with `Hol built successfully`; `Holmake --help` exited zero,
and `hol heapname` selected this checkout's `bin/hol.state`.  A preceding
default build completed its theory phase but its optional help generator
deadlocked while processing `smlOpen.view_struct.smd`; repeated samples showed
both fork participants waiting with zero CPU and a zero-byte output for nine
minutes.  The supported `--no-helpdocs` completion avoids that unrelated
documentation path.  No CakeML Dopen theory target had been run at the time of
this audit, so the commands below are the exact gates to execute rather than a
claim that they already pass.

Audit the historical delta without checking it out:

```sh
git -C /project/repos/cakeml merge-base \
  dcc03f2866f05b1db18b9f45c731ce45c3a3133e \
  db69b70e9ee28abd5d144e210a8fc6a396be4454
git -C /project/repos/cakeml rev-list --left-right --count \
  dcc03f2866f05b1db18b9f45c731ce45c3a3133e...\
db69b70e9ee28abd5d144e210a8fc6a396be4454
git -C /project/repos/cakeml diff --stat \
  5204d423c1b89d92a970f41f52da476d6cfb1e47..\
db69b70e9ee28abd5d144e210a8fc6a396be4454 -- semantics
```

Once a semantic slice is introduced, use the isolated current HOL checkout
and one CakeML build worker.  These are ordered narrow gates; stop at the
first failure and record it rather than skipping ahead:

```sh
export HOLDIR=/project/worktrees/HOL-cakeml-dopen-v13
cd /project/worktrees/cakeml-dopen-v13/semantics
"$HOLDIR/bin/Holmake" -j 1 \
  namespaceTheory.uo astTheory.uo gramTheory.uo \
  cmlPtreeConversionTheory.uo semanticPrimitivesTheory.uo \
  evaluateTheory.uo typeSystemTheory.uo

cd /project/worktrees/cakeml-dopen-v13/semantics/proofs
"$HOLDIR/bin/Holmake" -j 1 namespacePropsTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/parsing/tests
"$HOLDIR/bin/Holmake" -j 1 cmlTestsTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/inference
"$HOLDIR/bin/Holmake" -j 1 inferTheory.uo infer_cvTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/inference/tests
"$HOLDIR/bin/Holmake" -j 1 dopenTestsTheory.uo

cd /project/worktrees/cakeml-dopen-v13/compiler/inference/proofs
"$HOLDIR/bin/Holmake" -j 1 \
  envRelTheory.uo inferSoundTheory.uo inferCompleteTheory.uo \
  type_dCanonTheory.uo

cd /project/worktrees/cakeml-dopen-v13/translator
"$HOLDIR/bin/Holmake" -j 1 evaluate_decTheory.uo ml_progTheory.uo
```

The complete A2/A3 change must then rebuild bootstrap inference translation
and the compiled Candle open slice; a green semantics-only build is not the
gate.

## Integration decision

Use current master as the implementation base and `dopen2` only as a source
of semantic ideas and candidate lemmas.  The current candidate implements one
path-based exposure delta and makes dynamic semantics, declarative typing,
parsing, inference, and source compilation consume it.  The next proof slice
must establish module-selection preservation for `env_rel`, repair the exact
result shape of declaration soundness, and then discharge lookup/shadowing,
well-formedness, identity/stamp, canonicalisation, completeness, CV, and
compiled-regression gates.  No Flyspeck source rewrite or inference bypass
counts as progress on this gate.
