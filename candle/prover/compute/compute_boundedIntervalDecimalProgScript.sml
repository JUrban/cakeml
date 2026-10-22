(* CakeML translation of the proved decimal-scale directed endpoint layer. *)
Theory compute_boundedIntervalDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedIntervalProg compute_boundedIntervalDecimal

val _ = translation_extends "compute_boundedIntervalProg";

val bounded_scaled_mul_floor64_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_def;
val bounded_scaled_mul_ceil64_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_def;
val bounded_interval64_product_from_pairs_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def;
val bounded_interval64_product_mixed_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_interval64_product_mixed_decimal_def;
val bounded_interval64_mul_unchecked_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def;
val bounded_interval64_mul_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def;

val _ = export_theory ();
