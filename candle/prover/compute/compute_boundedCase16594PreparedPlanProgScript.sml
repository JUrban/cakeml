(* CakeML translation of the checked pinned case16594 plan compiler. *)
Theory compute_boundedCase16594PreparedPlanProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedAnalyticProgramProg compute_boundedCase16594PreparedPlan

val _ = translation_extends "compute_boundedAnalyticProgramProg";

val _ = register_type ``:bounded_poly_instruction``;
val _ = register_type ``:bounded_analytic_instruction``;
val _ = register_type ``:bounded_analytic_specialization``;

val bounded_case16594_program_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_case16594_program_def;
val bounded_analytic_specialization_program_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def;
val bounded_analytic_specialization_ok_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def;
val bounded_case16594_specializations_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_case16594_specializations_def;
val bounded_case16594_constant64_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_constant64_def;
val bounded_case16594_compile_poly_instruction_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_poly_instruction_def;
val bounded_case16594_compile_poly_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_poly_def;
val bounded_case16594_compile_analytic_instruction_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_instruction_def;
val bounded_case16594_compile_analytic_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_analytic_def;
val bounded_case16594_compile_specialized_instruction_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_instruction_def;
val bounded_case16594_compile_specialized_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_compile_specialized_def;
val bounded_case16594_prepared_program_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_def;
val bounded_case16594_prepared_program_ok_v =
  translate
    compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_ok_def;

val _ = export_theory ();
