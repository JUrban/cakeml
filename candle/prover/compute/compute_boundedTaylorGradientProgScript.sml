(* CakeML translation of checked gradient and compact Taylor completion. *)
Theory compute_boundedTaylorGradientProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorCompleteProg compute_boundedTaylorGradient

val _ = translation_extends "compute_boundedTaylorCompleteProg";

val bounded_signed64_scale40_128_v =
  translate
    compute_boundedTaylorGradientTheory.bounded_signed64_scale40_128_def;
val bounded128_low40_nonzero_v =
  translate
    compute_boundedTaylorGradientTheory.bounded128_low40_nonzero_def;
val bounded_signed128_shift_floor40_64_v =
  translate
    compute_boundedTaylorGradientTheory.bounded_signed128_shift_floor40_64_def;
val bounded_signed128_shift_ceil40_64_v =
  translate
    compute_boundedTaylorGradientTheory.bounded_signed128_shift_ceil40_64_def;
val bounded_hessian64_rows_v =
  translate compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def;
val bounded_taylor_gradient_row_complete_v =
  translate
    compute_boundedTaylorGradientTheory.bounded_taylor_gradient_row_complete_def;
val bounded_taylor_gradient_rows_complete_v =
  translate
    compute_boundedTaylorGradientTheory.bounded_taylor_gradient_rows_complete_def;
val bounded_taylor_gradient_complete_v =
  translate
    compute_boundedTaylorGradientTheory.bounded_taylor_gradient_complete_def;
val bounded_taylor64_complete_v =
  translate compute_boundedTaylorGradientTheory.bounded_taylor64_complete_def;

val _ = export_theory ();
