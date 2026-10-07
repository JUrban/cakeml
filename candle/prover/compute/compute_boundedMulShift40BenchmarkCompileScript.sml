(*
  Verified x64 compilation of the product-plus-shift benchmark.
*)
Theory compute_boundedMulShift40BenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedMulShift40BenchmarkProg

Theorem compute_bounded_mul_shift40_benchmark_compiled =
  eval_cake_compile_x64 "mul_shift40_"
    compute_bounded_mul_shift40_benchmark_prog_def
    "compute_bounded_mul_shift40_benchmark.S";

val _ = export_theory ();
