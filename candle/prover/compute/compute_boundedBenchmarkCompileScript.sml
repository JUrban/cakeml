(*
  Verified x64 compilation of the two closed bounded-compute benchmarks.
*)
Theory compute_boundedBenchmarkCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedAddBenchmarkProg compute_boundedControlBenchmarkProg

Theorem compute_bounded_add_benchmark_compiled =
  eval_cake_compile_x64 "add_" compute_bounded_add_benchmark_prog_def
    "compute_bounded_add_benchmark.S";

Theorem compute_bounded_control_benchmark_compiled =
  eval_cake_compile_x64 "control_" compute_bounded_control_benchmark_prog_def
    "compute_bounded_control_benchmark.S";

val _ = export_theory ();
