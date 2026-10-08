(* Verified CakeML program for the streaming genuine polynomial-only batch. *)
Theory compute_boundedCase16594StreamingPolynomialBatchProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase16594PreparedPlanProg
  compute_boundedCase16594StreamingPolynomialBatch

val _ = translation_extends "compute_boundedCase16594PreparedPlanProg";

val _ = register_type ``:bounded_case16594_streaming_input``;

val bounded_case16594_streaming_input_at_v =
  translate
    compute_boundedCase16594StreamingInputDataTheory.bounded_case16594_streaming_input_at_def;
val bounded_case16594_streaming_positive_intervals_v =
  translate
    compute_boundedCase16594PreparedInputTheory.bounded_case16594_positive_intervals_def;
val bounded_case16594_streaming_analytic64_nth_v =
  translate
    compute_boundedCase16594StreamingPolynomialBatchTheory.bounded_case16594_streaming_analytic64_nth_def;
val bounded_case16594_eval_streaming_polynomial_v =
  translate
    compute_boundedCase16594StreamingPolynomialBatchTheory.bounded_case16594_eval_streaming_polynomial_def;
val bounded_case16594_eval_streaming_polynomial_batch_v =
  translate
    compute_boundedCase16594StreamingPolynomialBatchTheory.bounded_case16594_eval_streaming_polynomial_batch_def;
val bounded_case16594_streaming_polynomial35_batch_v =
  translate
    compute_boundedCase16594StreamingPolynomialBatchTheory.bounded_case16594_streaming_polynomial35_batch_def;
val bounded_case16594_streaming_polynomial35_batch_ok_v =
  translate
    compute_boundedCase16594StreamingPolynomialBatchTheory.bounded_case16594_streaming_polynomial35_batch_ok_def;

Quote main = cakeml:
  if bounded_case16594_streaming_polynomial35_batch_ok () then ()
  else raise Bind;
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

Definition compute_bounded_case16594_streaming_polynomial35_batch_prog_def:
  compute_bounded_case16594_streaming_polynomial35_batch_prog = ^prog
End

val _ = export_theory ();
