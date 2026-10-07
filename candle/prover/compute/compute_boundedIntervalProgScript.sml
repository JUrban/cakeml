(* CakeML translation of sign-classified checked interval multiplication. *)
Theory compute_boundedIntervalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedSignedEndpointProg compute_boundedInterval

val _ = translation_extends "compute_boundedSignedEndpointProg";

val _ = register_type ``:bounded_interval64``;

val bounded_interval64_lower_v =
  translate compute_boundedIntervalTheory.bounded_interval64_lower_def;
val bounded_interval64_upper_v =
  translate compute_boundedIntervalTheory.bounded_interval64_upper_def;
val bounded_signed64_nonnegative_v =
  translate compute_boundedIntervalTheory.bounded_signed64_nonnegative_def;
val bounded_signed64_nonpositive_v =
  translate compute_boundedIntervalTheory.bounded_signed64_nonpositive_def;
val bounded_scaled_mul_floor64_v =
  translate compute_boundedIntervalTheory.bounded_scaled_mul_floor64_def;
val bounded_scaled_mul_ceil64_v =
  translate compute_boundedIntervalTheory.bounded_scaled_mul_ceil64_def;
val bounded_interval64_product_from_pairs_v =
  translate
    compute_boundedIntervalTheory.bounded_interval64_product_from_pairs_def;
val bounded_interval64_product_mixed_v =
  translate compute_boundedIntervalTheory.bounded_interval64_product_mixed_def;
val bounded_interval64_mul_unchecked_v =
  translate compute_boundedIntervalTheory.bounded_interval64_mul_unchecked_def;
val bounded_interval64_valid_v =
  translate compute_boundedIntervalTheory.bounded_interval64_valid_def;
val bounded_interval64_mul_v =
  translate compute_boundedIntervalTheory.bounded_interval64_mul_def;

val _ = export_theory ();
