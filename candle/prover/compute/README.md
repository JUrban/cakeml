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
