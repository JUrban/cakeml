(* CakeML translation of the proved decimal-scale directed endpoint layer. *)
Theory compute_boundedIntervalDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedSignedEndpointProg compute_boundedIntervalDecimal

val _ = translation_extends "compute_boundedSignedEndpointProg";

val bounded_scaled_mul_floor64_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_def;
val bounded_scaled_mul_ceil64_decimal_v =
  translate
    compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_def;

val _ = export_theory ();
