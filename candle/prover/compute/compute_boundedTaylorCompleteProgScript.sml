(* CakeML translation of compact checked Taylor value completion. *)
Theory compute_boundedTaylorCompleteProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedWideSignedProg compute_boundedTaylorComplete

val _ = translation_extends "compute_boundedWideSignedProg";

val bounded_interval64_abs_upper_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_interval64_abs_upper_def;
val bounded_word64_product128_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_word64_product128_def;
val bounded_dot_abs_upper_acc_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def;
val bounded_dot_abs_upper_v =
  translate compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_def;
val bounded_taylor_radius_pairs_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def;
val bounded_quadratic_abs_upper_acc_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def;
val bounded_quadratic_abs_upper_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_def;
val bounded_taylor_error_v =
  translate compute_boundedTaylorCompleteTheory.bounded_taylor_error_def;
val bounded_taylor_value_complete_v =
  translate
    compute_boundedTaylorCompleteTheory.bounded_taylor_value_complete_def;

val _ = export_theory ();
