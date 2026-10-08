(* Verified x64 compilation of the development-only first-cell state trace. *)
Theory compute_boundedCase16594StateTraceCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase16594StateTraceProg

Theorem compute_bounded_case16594_state_trace_compiled =
  eval_cake_compile_x64 "bounded_case16594_state_trace_"
    compute_bounded_case16594_state_trace_prog_def
    "compute_bounded_case16594_state_trace.S";

val _ = export_theory ();
