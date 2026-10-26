(* Add the pinned case-16594 plan compiler and streaming checker to the
 * shared case-10173/case-16594 translation environment.  This theory has no
 * command-line main; the stable four-payload program is defined downstream. *)
Theory compute_registeredNLCase16594CheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_registeredNLCase16594AnalyticProg
  compute_boundedCase16594PreparedPlan
  compute_boundedPackedSequentialCase16594Check

val _ = translation_extends "compute_registeredNLCase16594AnalyticProg";

val _ = register_type ``:bounded_poly_instruction``;
val _ = register_type ``:bounded_analytic_instruction``;
val _ = register_type ``:bounded_analytic_specialization``;

val _ = translate
  compute_boundedCase16594ProgramDataTheory.bounded_case16594_program_def;
val _ = translate
  compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def;
val _ = translate
  compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def;
val _ = translate
  compute_boundedCase16594ProgramDataTheory.bounded_case16594_specializations_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_constant64_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_poly_instruction_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_poly_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_instruction_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_instruction_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_def;
val _ = translate
  compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_ok_def;

val _ = translate
  compute_boundedPackedInputTheory.bounded_packed_interval64_zero_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_aux_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_positive_interval64_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_positive_interval64_list_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_list_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_list_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_input_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_analytic64_certificate_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_analytic64_certificate_list_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_cell_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_prefix_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_header_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_case16594_result_accepts_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_eval_cell_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_check_cells_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_complete_check_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_cell_status_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_first_status_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_cell_status8_def;
val _ = translate
  compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_first_status8_def;

val _ = export_theory ();
