(* Verified x64 compilation of the cell-220 state discriminator. *)
Theory compute_boundedCase16594Cell220StateTraceCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase16594Cell220StateTraceProg

Theorem compute_bounded_case16594_cell220_state_trace_compiled =
  eval_cake_compile_x64 "bounded_case16594_cell220_state_trace_"
    compute_bounded_case16594_cell220_state_trace_prog_def
    "compute_bounded_case16594_cell220_state_trace.S";

val _ = export_theory ();
