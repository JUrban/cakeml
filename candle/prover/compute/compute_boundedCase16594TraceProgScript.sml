(*
  Closed verified program for the authenticated case16594 operation-count
  trace.  The result check covers every loop and explicit overflow fallback.
*)
Theory compute_boundedCase16594TraceProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedProg

val _ = translation_extends "compute_boundedProg";

val bounded_case16594_sign_trace_v =
  translate compute_boundedTheory.bounded_case16594_sign_trace_def;
val bounded_case16594_sign_trace_result_ok_v =
  translate compute_boundedTheory.bounded_case16594_sign_trace_result_ok_def;
val bounded_case16594_sign_trace_overflow128_ok_v =
  translate
    compute_boundedTheory.bounded_case16594_sign_trace_overflow128_ok_def;
val bounded_case16594_sign_trace_overflow192_ok_v =
  translate
    compute_boundedTheory.bounded_case16594_sign_trace_overflow192_ok_def;
val bounded_case16594_sign_trace_ok_v =
  translate compute_boundedTheory.bounded_case16594_sign_trace_ok_def;

Quote main = cakeml:
  if bounded_case16594_sign_trace_ok () then () else raise Bind;
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_bounded_case16594_trace_prog_def:
  compute_bounded_case16594_trace_prog = ^prog
End

val _ = export_theory ();
