(* CakeML translation of the decimal historical dihedral center jet. *)
Theory compute_boundedHistoricalDihedralFirstDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedHistoricalDeltaDecimalProg
  compute_boundedHistoricalDihedralFirstDecimal

val _ = translation_extends "compute_boundedHistoricalDeltaDecimalProg";

(* Scale-independent helpers from the historical implementation. *)
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_interval64_nth_def;
val _ = translate compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_signed_terms_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_apply_signed_terms_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_component_from_products_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_negative_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_positive_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_negative_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_positive_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstTheory.bounded_historical_replace_three_def;

val _ = translate bounded_interval64_list_pairwise_mul_decimal_def;
val _ = translate bounded_delta64_pair_products_decimal_def;
val _ = translate bounded_historical_u_block_decimal_def;
val _ = translate bounded_historical_u_three_decimal_def;
val _ = translate bounded_historical_u126_decimal_def;
val _ = translate bounded_historical_u135_decimal_def;
val _ = translate bounded_historical_delta_x4_value_decimal_def;
val _ = translate bounded_historical_c_vector_decimal_def;
val _ = translate bounded_historical_pi_half_decimal_def;
val _ = translate bounded_historical_dihedral_first64_decimal_def;

val _ = export_theory ();
