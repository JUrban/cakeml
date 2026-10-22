(*
  Verified x64 compilation of the authenticated case16594 operation trace.
*)
Theory compute_boundedCase16594TraceCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase16594TraceProg

Theorem compute_bounded_case16594_trace_compiled =
  eval_cake_compile_x64 "case16594_trace_"
    compute_bounded_case16594_trace_prog_def
    "compute_bounded_case16594_trace.S";

val _ = export_theory ();
