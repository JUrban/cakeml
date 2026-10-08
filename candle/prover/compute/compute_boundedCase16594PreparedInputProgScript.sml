(* CakeML translation of the checked pinned case16594 prepared input zipper. *)
Theory compute_boundedCase16594PreparedInputProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedCase16594PreparedPlanProg
  compute_boundedCase16594PreparedInput

val _ = translation_extends "compute_boundedCase16594PreparedPlanProg";

val _ = register_type ``:bounded_case16594_input``;
val _ = register_type ``:bounded_case16594_center_radius_input``;
val _ = register_type ``:bounded_case16594_prepared_input``;

val bounded_case16594_inputs_v =
  translate
    compute_boundedCase16594InputDataTheory.bounded_case16594_inputs_def;
val bounded_case16594_center_radius_inputs_v =
  translate
    compute_boundedCase16594CenterRadiusDataTheory.bounded_case16594_center_radius_inputs_def;
val bounded_case16594_positive_intervals_v =
  translate
    compute_boundedCase16594PreparedInputTheory.bounded_case16594_positive_intervals_def;
val bounded_case16594_prepare_input_v =
  translate
    compute_boundedCase16594PreparedInputTheory.bounded_case16594_prepare_input_def;
val bounded_case16594_prepare_inputs_v =
  translate
    compute_boundedCase16594PreparedInputTheory.bounded_case16594_prepare_inputs_def;
val bounded_case16594_prepared_inputs_v =
  translate
    compute_boundedCase16594PreparedInputTheory.bounded_case16594_prepared_inputs_def;
val bounded_case16594_prepared_inputs_ok_v =
  translate
    compute_boundedCase16594PreparedInputTheory.bounded_case16594_prepared_inputs_ok_def;

val _ = export_theory ();
