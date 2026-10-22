(* CakeML translation of the complete decimal case-10173 cell checker. *)
Theory compute_boundedCase10173HistoricalCellDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedHistoricalDihedralSecondDecimalProg
  compute_boundedCase10173HistoricalCellDecimal

val _ = translation_extends
  "compute_boundedHistoricalDihedralSecondDecimalProg";

val _ = register_type ``:bounded_case10173_sqrt64_certificate``;

(* Scale-independent cell structure and guards. *)
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def;
val _ = translate
  compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def;
val _ = translate
  compute_boundedCase10173HistoricalCellTheory.bounded_case10173_defer_def;
val _ = translate
  compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_add_def;
val _ = translate
  compute_boundedCase10173HistoricalCellTheory.bounded_case10173_radius_covers_def;
val _ = translate
  compute_boundedCase10173HistoricalCellTheory.bounded_case10173_geometry_ok_def;
val _ = translate
  compute_boundedCase10173HistoricalCellTheory.bounded_case10173_positive_environment_def;
val _ = translate
  compute_boundedCase10173HistoricalCellTheory.bounded_case10173_angle_state_def;

val _ = translate bounded_interval64_unit_vector_decimal_def;
val _ = translate bounded_taylor64_variable_decimal_def;
val _ = translate bounded_case10173_root_coefficients_decimal_def;
val _ = translate bounded_case10173_source_constant_decimal_def;
val _ = translate bounded_case10173_angle_coefficient_decimal_def;
val _ = translate bounded_case10173_deferred_scale_decimal_def;
val _ = translate bounded_case10173_u_guards_decimal_def;
val _ = translate bounded_case10173_add_coordinate_sqrts_decimal_def;
val _ = translate bounded_case10173_complete_deferred_decimal_def;
val _ = translate bounded_case10173_checked_cell64_decimal_def;
val _ = translate bounded_case10173_checked_cell_accepts_decimal_def;

val _ = export_theory ();
