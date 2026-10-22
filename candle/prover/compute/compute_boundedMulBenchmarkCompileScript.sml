(*
  Verified x64 compilation of the hybrid full-product benchmark pair.
*)
Theory compute_boundedMulBenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedMulBenchmarkProg compute_boundedMulControlBenchmarkProg

Theorem compute_bounded_mul_benchmark_compiled =
  eval_cake_compile_x64 "mul_" compute_bounded_mul_benchmark_prog_def
    "compute_bounded_mul_benchmark.S";

Theorem compute_bounded_mul_control_benchmark_compiled =
  eval_cake_compile_x64 "mul_control_"
    compute_bounded_mul_control_benchmark_prog_def
    "compute_bounded_mul_control_benchmark.S";

val _ = export_theory ();
