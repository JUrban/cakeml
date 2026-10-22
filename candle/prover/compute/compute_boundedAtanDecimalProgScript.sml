(* CakeML translation of checked decimal fixed-scale arctangent evaluation. *)
Theory compute_boundedAtanDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorSqrtDecimalProg compute_boundedAtanDecimal

val _ = translation_extends "compute_boundedTaylorSqrtDecimalProg";

val _ = translate bounded_atan_scale_decimal_def;
val _ = translate bounded_atan_one_decimal_def;
val _ = translate bounded_atan_pi_half_decimal_def;
val _ = translate bounded_atan_pos_third_decimal_def;
val _ = translate bounded_atan_neg_third_decimal_def;
val _ = translate bounded_atan_pos_fifth_decimal_def;
val _ = translate bounded_atan_neg_seventh_decimal_def;
val _ = translate bounded_atan_pos_ninth_decimal_def;
val _ = translate bounded_atan_neg_eleventh_decimal_def;
val _ = translate bounded_atan_pos_thirteenth_decimal_def;
val _ = translate bounded_interval64_mul_add_decimal_def;
val _ = translate bounded_interval64_atan_pos_lower_decimal_def;
val _ = translate bounded_interval64_atan_pos_upper_decimal_def;
val _ = translate bounded_interval64_atan_unit_lower_decimal_def;
val _ = translate bounded_interval64_atan_unit_upper_decimal_def;
val _ = translate bounded_interval64_atan_unit_decimal_def;
val _ = translate bounded_interval64_atan_range_point_decimal_def;
val _ = translate bounded_interval64_atan_range_decimal_def;

val _ = export_theory ();
