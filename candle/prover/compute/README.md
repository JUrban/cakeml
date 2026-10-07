A verified Candle compute primitive.

[compute_boundedScript.sml](compute_boundedScript.sml):
Lossless checked 128- and 192-bit limb boundaries for experimental bounded
compute execution, with total option-valued add, multiply-to-wide, and
narrowing/directed-dyadic-shift contracts for a future word-level
implementation.  The first executable primitives are checked two- and
three-limb Word64 additions, proved equal to their exact option-valued
contracts.  The executable multiplication probes include a general exact
Word64-by-Word64 full product built from 22-bit small-natural convolution;
its high/low result is proved to reconstruct the mathematical product.

[compute_boundedProgScript.sml](compute_boundedProgScript.sml):
Verified CakeML translations of the Word64-only carry primitive and the
checked two- and three-limb additions.  The executable carry path deliberately
contains no conversion through unbounded naturals.  This theory also translates
the exact 22-bit-radix multiplication primitive and its closed benchmark loop.

[compute_boundedAddBenchmarkProgScript.sml](compute_boundedAddBenchmarkProgScript.sml)
and
[compute_boundedControlBenchmarkProgScript.sml](compute_boundedControlBenchmarkProgScript.sml):
Closed result-checking programs for a ten-million-iteration checked-add
workload and its matched recursion/constructor control.

[compute_boundedBenchmarkCompileScript.sml](compute_boundedBenchmarkCompileScript.sml):
Verified x64 compilation of the closed bounded-add benchmark pair.

[compute_boundedMulBenchmarkProgScript.sml](compute_boundedMulBenchmarkProgScript.sml),
[compute_boundedMulControlBenchmarkProgScript.sml](compute_boundedMulControlBenchmarkProgScript.sml),
and
[compute_boundedMulBenchmarkCompileScript.sml](compute_boundedMulBenchmarkCompileScript.sml):
Closed result-checking programs and verified x64 compilation for the exact but
conversion-heavy multiplication fallback and its matched recursion control.

[compute_boundedMulChunks22BenchmarkProgScript.sml](compute_boundedMulChunks22BenchmarkProgScript.sml)
and
[compute_boundedMulChunks22BenchmarkCompileScript.sml](compute_boundedMulChunks22BenchmarkCompileScript.sml):
Closed result-checking program and verified x64 compilation for ten million
applications of the proved 22-bit-radix full-word multiplication primitive.

[compute_boundedMulShift40BenchmarkProgScript.sml](compute_boundedMulShift40BenchmarkProgScript.sml)
and
[compute_boundedMulShift40BenchmarkCompileScript.sml](compute_boundedMulShift40BenchmarkCompileScript.sml):
Closed result-checking program and verified x64 compilation for the real hot
endpoint boundary: a full Word64 product followed by the case16594 dyadic
`2^40` floor shift back into a two-word endpoint.

[compute_boundedSignedScript.sml](compute_boundedSignedScript.sml) and
[compute_boundedSignedProgScript.sml](compute_boundedSignedProgScript.sml):
Canonical signed-magnitude endpoints and CakeML translations for exact
`2^40` directed products.  The theory proves the low-bit remainder test,
total ceiling correction, canonical zero, result signs, and floor/ceiling
magnitudes while retaining the explicit option-valued overflow boundary.

[compute_boundedSignedAddScript.sml](compute_boundedSignedAddScript.sml) and
[compute_boundedSignedAddProgScript.sml](compute_boundedSignedAddProgScript.sml):
Checked two-word comparison, subtraction with borrow, and canonical signed
accumulation.  The proofs connect every successful subtraction to exact
natural-number difference, preserve explicit same-sign overflow, and ensure
that every produced signed endpoint is normalized before CakeML translation.

[compute_boundedSignedEndpointScript.sml](compute_boundedSignedEndpointScript.sml)
and
[compute_boundedSignedEndpointProgScript.sml](compute_boundedSignedEndpointProgScript.sml):
The proved boundary between wide intermediate values and one-word stored
signed endpoints.  Narrowing succeeds exactly below `2^64`, rejects a nonzero
high limb, and canonicalizes negative zero.  Signed comparison and min/max
are proved equal to mathematical integer order even for noncanonical input
encodings.  All hot-path endpoint operations translate to CakeML.

[compute_boundedSignedEndpointAddScript.sml](compute_boundedSignedEndpointAddScript.sml)
and
[compute_boundedSignedEndpointAddProgScript.sml](compute_boundedSignedEndpointAddProgScript.sml):
Exact stored signed-endpoint negation and checked addition.  Addition widens
through the existing signed 128-bit accumulator and explicitly narrows back to
one word; every successful result is canonical and denotes the exact integer
sum, while overflow remains `NONE`.  Mixed signs, cancellation, negative-zero
normalization, and overflow have closed executable tests, and both operations
translate to CakeML.

[compute_boundedIntervalScript.sml](compute_boundedIntervalScript.sml) and
[compute_boundedIntervalProgScript.sml](compute_boundedIntervalProgScript.sml):
Executable sign-classified interval multiplication over stored signed
endpoints.  All nine sign combinations use the proved directed `2^40`
Word64 product and explicit one-word narrowing; the mixed/mixed case computes
the two necessary lower and upper candidates.  A checked wrapper rejects
invalid input intervals, while the hot unchecked operation is reserved for
states covered by validity-preservation proofs.  Closed exact sign-class and
overflow tests pass.  The general interval-containment/preservation theorem
is still a DEVELOPMENT obligation before this operation can support a release
claim.

[compute_boundedIntervalAddScript.sml](compute_boundedIntervalAddScript.sml)
and
[compute_boundedIntervalAddProgScript.sml](compute_boundedIntervalAddProgScript.sml):
Exact fixed-scale interval negation and checked addition.  General theorems
prove endpoint values, normalization, validity preservation, and fail-closed
invalid-input/overflow behavior.  These are the last basic linear operations
needed to assemble the genuine-box evaluator; both translate to CakeML.

[compute_boundedCase16594TraceProgScript.sml](compute_boundedCase16594TraceProgScript.sml)
and
[compute_boundedCase16594TraceCompileScript.sml](compute_boundedCase16594TraceCompileScript.sml):
Closed result-checking program and verified x64 compilation for the genuine
authenticated case16594 operation counts: sign classification, full-word
products, checked 128/192 additions, directed shifts, narrowing branches, and
explicit overflow rejection.

[generate_case16594_actual_data.py](generate_case16594_actual_data.py),
[compute_boundedCase16594ActualDataScript.sml](compute_boundedCase16594ActualDataScript.sml),
[compute_boundedCase16594ActualProgScript.sml](compute_boundedCase16594ActualProgScript.sml),
and
[compute_boundedCase16594ActualCompileScript.sml](compute_boundedCase16594ActualCompileScript.sml):
First actual-data boundary for that trace.  The generator accepts only the
pinned 875-row case16594 export and emits exact `2^40` encodings of one genuine
lower-coordinate product per cell.  HOL checks the data length and complete
product digest; the translated closed program executes every pair through the
proved Word64 product/shift operation and is compiled to verified x64.  This
is a DEVELOPMENT data-flow slice, not yet the complete nonlinear checker or a
source-correspondence theorem.

[generate_case16594_input_data.py](generate_case16594_input_data.py),
[compute_boundedCase16594InputDataScript.sml](compute_boundedCase16594InputDataScript.sml),
and
[compute_boundedCase16594InputProgScript.sml](compute_boundedCase16594InputProgScript.sml):
Complete reusable input boundary for the same 875 cells.  Each record contains
the six directed box intervals and the ten box and ten center square-root
certificate intervals, for 45,500 pinned-source `word64` endpoints in total.
HOL checks the record count and a closed digest; the translator exposes the
typed cell constant without translating the proof-only polymorphic digest
helper.  The generator and this data remain DEVELOPMENT / NON-RELEASE pending
the general source-correspondence theorem.

[generate_case16594_program_data.py](generate_case16594_program_data.py),
[compute_boundedCase16594ProgramDataScript.sml](compute_boundedCase16594ProgramDataScript.sml),
[compute_boundedDeltaSpecializationScript.sml](compute_boundedDeltaSpecializationScript.sml),
and
[compute_boundedCase16594ProgramProgScript.sml](compute_boundedCase16594ProgramProgScript.sml):
Pinned typed import of the complete 167-instruction analytic source program.
The generator checks the exact cval hash, nested polynomial postfix stacks,
outer analytic stack, ten square-root placeholders, and all constructor
tags.  HOL rechecks the 167-to-one stack transition and exact specialization
program identities (including same-length alias rejections), and CakeML
translates both the data and the total validators.  The six
delta-family postfix programs now have universal integer-polynomial semantics
theorems: the three radicands equal `4*x_i*delta`, and exact symmetric-
difference identities characterize the other three as the named negative
delta derivatives.  The lift into the general analytic/rational source
theorem remains a release obligation.  No runtime dispatch may authorize a
role from its list position or instruction length alone.

[compute_boundedDeltaGradient0Script.sml](compute_boundedDeltaGradient0Script.sml),
[compute_boundedDeltaGradient0ProgScript.sml](compute_boundedDeltaGradient0ProgScript.sml),
and
[compute_boundedDeltaGradient0CompileScript.sml](compute_boundedDeltaGradient0CompileScript.sml):
First complete actual-data delta-family instruction.  It evaluates component
zero of `grad(delta)` on every authenticated box using ten directed interval
products and checked canonical signed accumulation, checks the complete
875-result digest, and produces a verified x64 executable.  This remains a
DEVELOPMENT instruction boundary rather than the complete Taylor verdict or
the eventual source-to-formula soundness theorem.

[compute_boundedDeltaGradient0BenchmarkProgScript.sml](compute_boundedDeltaGradient0BenchmarkProgScript.sml)
and
[compute_boundedDeltaGradient0BenchmarkCompileScript.sml](compute_boundedDeltaGradient0BenchmarkCompileScript.sml):
Closed in-process benchmark that repeats the entire 875-cell instruction one
thousand times and checks the count/digest after every iteration.  This
separates recurring verified word execution from process and constant-loading
cost without weakening the fail-closed result boundary.

[compute_boundedDeltaGradient0FlatScript.sml](compute_boundedDeltaGradient0FlatScript.sml),
[compute_boundedDeltaGradient0FlatBenchmarkProgScript.sml](compute_boundedDeltaGradient0FlatBenchmarkProgScript.sml),
and
[compute_boundedDeltaGradient0FlatBenchmarkCompileScript.sml](compute_boundedDeltaGradient0FlatBenchmarkCompileScript.sml):
Allocation discriminator that removes transient product/signed-sum lists from
the hot path.  General HOL theorems prove the flat box, batch, and acceptance
predicate extensionally equal to the original total instruction before its
closed thousand-batch benchmark is translated and compiled.

[computeProofScript.sml](computeProofScript.sml):
Proof of correctness for the compute primitive.

[computeScript.sml](computeScript.sml):
Implementation of the compute primitive.

[compute_evalProofScript.sml](compute_evalProofScript.sml):
Proofs about the interpreter function for the Candle compute primitive.

[compute_evalScript.sml](compute_evalScript.sml):
Interpreter function for the Candle compute primitive.

[compute_execProofScript.sml](compute_execProofScript.sml):
Verification of fast interpreter for the Candle compute primitive.

[compute_execScript.sml](compute_execScript.sml):
Fast interpreter function for the Candle compute primitive.

[compute_pmatchScript.sml](compute_pmatchScript.sml):
Pmatch definitions for functions in computeScript.sml.

[compute_syntaxProofScript.sml](compute_syntaxProofScript.sml):
Proofs related to term embeddings for the Candle compute primitive.

[compute_syntaxScript.sml](compute_syntaxScript.sml):
Definitions of 'compute expressions' for the Candle compute primitive.
