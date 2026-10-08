(* Verified x64 compilation of the complete-batch failure localizer. *)
Theory compute_boundedCase16594BatchStatusCompile
Libs
  preamble eval_cake_compile_x64Lib
Ancestors
  compute_boundedCase16594BatchStatusProg

Theorem compute_bounded_case16594_batch_status_compiled =
  eval_cake_compile_x64 "bounded_case16594_batch_status_"
    compute_bounded_case16594_batch_status_prog_def
    "compute_bounded_case16594_batch_status.S";

val _ = export_theory ();
