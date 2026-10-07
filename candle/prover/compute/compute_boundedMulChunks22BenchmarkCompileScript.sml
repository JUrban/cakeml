(*
  Verified x64 compilation of the 22-bit-chunk product benchmark.
*)
Theory compute_boundedMulChunks22BenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedMulChunks22BenchmarkProg

Theorem compute_bounded_mul_chunks22_benchmark_compiled =
  eval_cake_compile_x64 "mul_chunks22_"
    compute_bounded_mul_chunks22_benchmark_prog_def
    "compute_bounded_mul_chunks22_benchmark.S";

val _ = export_theory ();
