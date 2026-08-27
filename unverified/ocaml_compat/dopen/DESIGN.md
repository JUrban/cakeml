# Declaration-open design slice

Status: review specification for the first A1--A3 implementation slice.
Expression `let open` is deliberately out of scope.  The Flyspeck manifest
inventory requires declaration open and contains no expression open.

## Representation and shared operation

The AST constructor is `Dopen locs (modN list)`.  A list represents the
non-empty module path in source order, so `open A.B` becomes
`Dopen locs [«A»; «B»]`.  Keeping a path, rather than the historical single
`modN`, avoids another AST migration when a later corpus needs nested open.

All semantic layers use one namespace operation:

```text
nsOpen []       env = NONE
nsOpen nonempty env = nsLookupMod env nonempty
```

Rejecting the empty path is important.  `nsLookupMod env [] = SOME env`, but
`Dopen []` is not source syntax and treating it as open would re-export the
whole current environment.

The dynamic, declarative-type, inference, and source-to-flat records contain
parallel namespaces.  Their small wrappers call `nsOpen path` for every
component and succeed only if every lookup succeeds.  A well-formed module
declaration creates the path in every component, including components whose
selected namespace is empty.

## Declaration result is a delta

On success, `Dopen path` returns exactly the selected module contents as its
declaration delta.  It does **not** append the current environment.  Existing
declaration-list machinery then performs the one intended extension:

```text
Dopen path  --returns-->  opened_delta
next declaration sees    opened_delta ++ current_env
whole list returns        later_deltas ++ opened_delta
```

Here `++` is the existing left-biased `nsAppend` component-wise.  This gives
the required precedence: names exposed by the most recent open shadow older
bindings, and declarations after an open shadow that open.  The original
qualified namespaces remain in the older environment; exact module-name
shadowing still follows `nsAppend`, as it does for ordinary module
declarations.

Returning `opened_delta ++ current_env` from `Dopen` would be wrong at this
interface: `evaluate_decs`, `type_ds`, `infer_ds`, and `compile_decs` would
append the current environment again during sequencing.  This is the
unresolved mismatch in historical `dopen2`; this design removes it rather
than trying to prove duplication harmless.

Opening is read-only.  Dynamic evaluation returns the input machine state.
Inference returns the input `infer_st` byte-for-byte: it allocates no uvars,
type IDs, exception stamps, or substitutions.

## Parser/elaboration boundary

The lexer already emits `OpenT`, and a dotted source name is one `LongidT`
containing a `tokens$path` plus its final component.  Parse-tree conversion
turns either a simple `StructName` or a `LongidT` into the non-empty AST list.
The constructor carries the declaration location so an absent module is an
ordinary located inference error.

The separate OCaml frontend has its own `nOpen` and recursive `nModulePath`
productions.  Its conversion now validates the `OpenT`, converts the successful
module path directly to the same non-empty AST list, preserves the declaration
location, and applies the existing `compatModName` mapping to every component
(for example `Text_io` becomes `TextIO`).  It does not route OCaml source
through the Standard ML grammar.

The current CakeML base has no active constructor-arity elaboration state.
`PCstate0.ctr_arities` and its state-monad scaffolding remain near the top of
`cmlPtreeConversionScript.sml`, but repository-wide reference analysis finds
no consumer of the field and the parser tests explicitly note that
`elab_decs` was removed.  The actual `ptree_Decl`/`ptree_Decls` conversion is
pure `option` code.  Constructors are recognized syntactically by uppercase
names, pattern application is accumulated by `Papply`, and expression
application to a constructor is accumulated by `mkAst_App`; constructor
arity is subsequently validated by type inference.

Consequently, this current-base A2 slice must not resurrect the dead parser
state merely to satisfy wording inherited from an older architecture.
Declaration open exposes the constructor namespace through `open_ienv.inf_c`;
the required gate is a parser-to-inference regression in which constructors
used after an open resolve with the selected arity, plus wrong-arity and
shadowing failures.  `cmlPtreeConversionProps$Decl_OK` still needs proof
coverage for the two open grammar productions; the branch now contains queued
proof branches for both.  If a future parser restores
stateful arity elaboration, that state will need the same proved namespace
selection operation before it can be accepted.

The branch has queued both pieces of this gate: `Decl_OK` branches for the
standard parser and source-to-inference tests for both `parse_prog` and the
OCaml-specific `caml_parser$run`.  They remain proof/test candidates until the
ordered HOL targets build.

## Proof obligations

The slice is not accepted merely because its equations execute.  At minimum:

1. `nsOpen` is `NONE` exactly on an empty or missing path, and a successful
   result is exactly `nsLookupMod` at that non-empty path.
2. Component wrappers agree under the dynamic/type/inference environment
   relations and preserve their well-formedness invariants.
3. Extending by the returned delta gives left-biased lookup precedence; a
   later declaration shadows the open; repeated open is idempotent at lookup
   level where no intervening declaration changes the selected module.
4. `infer_d` success for `Dopen` leaves the entire `infer_st` unchanged.
5. Inference soundness constructs the corresponding `type_d Dopen` rule;
   completeness and canonicalisation transport the same selected delta.
6. Type identities inside the opened delta are existing identities.  Opening
   creates no IDs and preserves the next-ID lower bound and stamp relations.
7. CV translation and bootstrap translation reproduce `infer_open` and its
   success/failure result; no untranslated host inference call is allowed.
8. Source-to-flat opening changes only the compiler environment and emits no
   flat declaration; its returned environment is the selected delta, so list
   compilation also extends it exactly once.
9. Functional, big-step, small-step, and itree declaration semantics agree on
   the delta result and on missing-path type errors.
10. AST S-expression round trips, AST syntax helpers/printers, free-variable
    traversals, and declaration-size termination arguments cover `Dopen`.

## Review tests

The first executable gates are:

- parser: `open A` maps to `[«A»]`, `open A.B.C` maps to
  `[«A»; «B»; «C»]`, and declaration location is retained;
- inference/semantics: value, constructor, exception, type-name, submodule,
  shadowing, repeated-open, and missing-path cases match the pinned OCaml
  oracle categories;
- state: a successful open returns the identical `infer_st` and unchanged
  dynamic stamp counters;
- sequencing: `val x = 0; open M; val y = x` uses `M.x`, while
  `open M; val x = 0; val y = x` uses the later `x`;
- compiled slice: an open-dependent program compiles after full inference and
  executes with the oracle output.

Until the proof stack and compiled slice pass, source rewriting, qualification
of Flyspeck names, and inference bypasses are explicitly not substitutes for
this gate.
