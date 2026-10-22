(* Verified x64 compilation of the decimal product/divide benchmark. *)
Theory compute_boundedMulDivDecimalBenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedMulDivDecimalBenchmarkProg

Theorem compute_bounded_mul_div_decimal_benchmark_compiled =
  eval_cake_compile_x64 "mul_div_decimal_"
    compute_bounded_mul_div_decimal_benchmark_prog_def
    "compute_bounded_mul_div_decimal_benchmark.S";

val _ = export_theory ();
