(* Verified x64 compilation of the flat gradient-0 recurring benchmark. *)
Theory compute_boundedDeltaGradient0FlatBenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedDeltaGradient0FlatBenchmarkProg

Theorem compute_bounded_delta_gradient0_flat_benchmark_compiled =
  eval_cake_compile_x64 "delta_gradient0_flat_benchmark_"
    compute_bounded_delta_gradient0_flat_benchmark_prog_def
    "compute_bounded_delta_gradient0_flat_benchmark.S";

val _ = export_theory ();
