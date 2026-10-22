(* CakeML translation of the decimal historical dihedral box jet. *)
Theory compute_boundedHistoricalDihedralSecondDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedHistoricalDihedralFirstDecimalProg
  compute_boundedHistoricalDihedralSecondDecimal

val _ = translation_extends
  "compute_boundedHistoricalDihedralFirstDecimalProg";

(* Scale-independent helpers not required by the center-only slice. *)
val _ = translate
  compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def;
val _ = translate
  compute_boundedIntervalListTheory.bounded_interval64_list_add_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_sums_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondTheory.bounded_historical_extreme_interval_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_environment_def;

val _ = translate bounded_historical_delta_gradient_component_decimal_def;
val _ = translate bounded_historical_delta_gradient_box_entry_decimal_def;
val _ = translate bounded_historical_delta_gradient_box_decimal_def;
val _ = translate bounded_historical_delta_second_decimal_def;
val _ = translate bounded_historical_delta_x4_value_block_decimal_def;
val _ = translate bounded_historical_delta_x4_hessian_decimal_def;
val _ = translate bounded_historical_delta_x4_second_decimal_def;
val _ = translate bounded_historical_sqrt_hessian_decimal_def;
val _ = translate bounded_historical_sqrt_second_decimal_def;
val _ = translate bounded_historical_b_hessian_decimal_def;
val _ = translate bounded_historical_second_hessian_entry_decimal_def;
val _ = translate bounded_historical_second_hessian_decimal_def;
val _ = translate bounded_historical_dihedral_second64_decimal_def;

val _ = export_theory ();
