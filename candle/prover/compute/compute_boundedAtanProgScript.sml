(* CakeML translation of checked fixed-scale arctangent data evaluation. *)
Theory compute_boundedAtanProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedReciprocalCertificateProg compute_boundedIntervalAddProg
  compute_boundedAtan

val _ = translation_extends "compute_boundedReciprocalCertificateProg";

val bounded_atan_word64_v =
  translate compute_boundedAtanTheory.bounded_atan_word64_def;
val bounded_atan_scale_v =
  translate compute_boundedAtanTheory.bounded_atan_scale_def;
val bounded_atan_one_v =
  translate compute_boundedAtanTheory.bounded_atan_one_def;
val bounded_atan_pi_half_v =
  translate compute_boundedAtanTheory.bounded_atan_pi_half_def;
val bounded_atan_pos_third_v =
  translate compute_boundedAtanTheory.bounded_atan_pos_third_def;
val bounded_atan_neg_third_v =
  translate compute_boundedAtanTheory.bounded_atan_neg_third_def;
val bounded_atan_pos_fifth_v =
  translate compute_boundedAtanTheory.bounded_atan_pos_fifth_def;
val bounded_atan_neg_seventh_v =
  translate compute_boundedAtanTheory.bounded_atan_neg_seventh_def;
val bounded_atan_pos_ninth_v =
  translate compute_boundedAtanTheory.bounded_atan_pos_ninth_def;
val bounded_atan_neg_eleventh_v =
  translate compute_boundedAtanTheory.bounded_atan_neg_eleventh_def;
val bounded_atan_pos_thirteenth_v =
  translate compute_boundedAtanTheory.bounded_atan_pos_thirteenth_def;
val bounded_interval64_mul_add_v =
  translate compute_boundedAtanTheory.bounded_interval64_mul_add_def;
val bounded_interval64_atan_pos_lower_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_pos_lower_def;
val bounded_interval64_atan_pos_upper_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_pos_upper_def;
val bounded_interval64_atan_unit_lower_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_unit_lower_def;
val bounded_interval64_atan_unit_upper_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_unit_upper_def;
val bounded_interval64_atan_unit_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_unit_def;
val bounded_interval64_atan_range_point_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_range_point_def;
val bounded_interval64_atan_range_v =
  translate compute_boundedAtanTheory.bounded_interval64_atan_range_def;

val _ = export_theory ();
