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
comments, strings, and backtick quotations and emits only unambiguous token
prefixes.  Its output must still be reviewed against the ordered production
manifest; it is not a replacement for parser acceptance tests.
