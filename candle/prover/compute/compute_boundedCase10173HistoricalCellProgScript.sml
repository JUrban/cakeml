(* CakeML translation of the complete genuine case-10173 historical cell. *)
Theory compute_boundedCase10173HistoricalCellProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedHistoricalDihedralSecondPackedCheckProg
  compute_boundedCase10173HistoricalCell

val _ = translation_extends
  "compute_boundedHistoricalDihedralSecondPackedCheckProg";

val _ = register_type ``:bounded_case10173_sqrt64_certificate``;

val bounded_case10173_root_coefficients_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_root_coefficients_def;
val bounded_case10173_source_constant_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_source_constant_def;
val bounded_case10173_angle_coefficient_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_angle_coefficient_def;
val bounded_case10173_defer_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_defer_def;
val bounded_case10173_deferred_scale_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_scale_def;
val bounded_case10173_deferred_add_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_add_def;
val bounded_case10173_radius_covers_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_radius_covers_def;
val bounded_case10173_geometry_ok_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_geometry_ok_def;
val bounded_case10173_positive_environment_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_positive_environment_def;
val bounded_case10173_u_guards_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_u_guards_def;
val bounded_case10173_add_coordinate_sqrts_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_add_coordinate_sqrts_def;
val bounded_case10173_angle_state_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_angle_state_def;
val bounded_case10173_complete_deferred_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_complete_deferred_def;
val bounded_case10173_checked_cell64_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_checked_cell64_def;
val bounded_case10173_checked_cell_accepts_v =
  translate
    compute_boundedCase10173HistoricalCellTheory.bounded_case10173_checked_cell_accepts_def;

val _ = export_theory ();
