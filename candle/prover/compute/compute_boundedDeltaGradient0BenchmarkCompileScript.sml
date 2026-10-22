(* Verified x64 compilation of the recurring gradient-0 batch benchmark. *)
Theory compute_boundedDeltaGradient0BenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedDeltaGradient0BenchmarkProg

Theorem compute_bounded_delta_gradient0_benchmark_compiled =
  eval_cake_compile_x64 "delta_gradient0_benchmark_"
    compute_bounded_delta_gradient0_benchmark_prog_def
    "compute_bounded_delta_gradient0_benchmark.S";

val _ = export_theory ();
