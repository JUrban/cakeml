(* CakeML translation of checked compact Taylor arctangent lifting. *)
Theory compute_boundedTaylorAtanProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorSqrtProg compute_boundedTaylorAtan

val _ = translation_extends "compute_boundedTaylorSqrtProg";

val bounded_interval64_square_unchecked_v =
  translate
    compute_boundedIntervalSquareTheory.bounded_interval64_square_unchecked_def;
val bounded_interval64_square_v =
  translate compute_boundedIntervalSquareTheory.bounded_interval64_square_def;
val bounded_taylor64_atan_v =
  translate compute_boundedTaylorAtanTheory.bounded_taylor64_atan_def;

val _ = export_theory ();
