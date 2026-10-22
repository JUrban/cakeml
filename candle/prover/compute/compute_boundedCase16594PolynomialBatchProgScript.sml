(* Verified CakeML program for the genuine case16594 polynomial-only batch. *)
Theory compute_boundedCase16594PolynomialBatchProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase16594PreparedInputProg
  compute_boundedCase16594PolynomialBatch

val _ = translation_extends "compute_boundedCase16594PreparedInputProg";

val bounded_case16594_analytic64_nth_v =
  translate
    compute_boundedCase16594PolynomialBatchTheory.bounded_case16594_analytic64_nth_def;
val bounded_case16594_eval_polynomial_v =
  translate
    compute_boundedCase16594PolynomialBatchTheory.bounded_case16594_eval_polynomial_def;
val bounded_case16594_eval_polynomial_batch_v =
  translate
    compute_boundedCase16594PolynomialBatchTheory.bounded_case16594_eval_polynomial_batch_def;
val bounded_case16594_polynomial35_batch_v =
  translate
    compute_boundedCase16594PolynomialBatchTheory.bounded_case16594_polynomial35_batch_def;
val bounded_case16594_polynomial35_batch_ok_v =
  translate
    compute_boundedCase16594PolynomialBatchTheory.bounded_case16594_polynomial35_batch_ok_def;

Quote main = cakeml:
  if bounded_case16594_polynomial35_batch_ok () then () else raise Bind;
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

Definition compute_bounded_case16594_polynomial35_batch_prog_def:
  compute_bounded_case16594_polynomial35_batch_prog = ^prog
End

val _ = export_theory ();
