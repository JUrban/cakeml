(* CakeML translation of the versioned generic analytic plan boundary. *)
Theory compute_boundedAnalyticPlanCVProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedAnalyticPreparedPlanProg
  compute_boundedAnalyticPlanCV

val _ = translation_extends "compute_boundedAnalyticPreparedPlanProg";

val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_rational_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_poly_instruction_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_poly_program_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_sqrt_placeholder_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def;
val _ = translate
  compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def;

val _ = register_type ``:bounded_analytic_plan_metadata``;

val bounded_analytic_plan_metadata_of_cv_v =
  translate
    compute_boundedAnalyticPlanCVTheory.bounded_analytic_plan_metadata_of_cv_def;
val bounded_analytic64_certificate_count_v =
  translate
    compute_boundedAnalyticPlanCVTheory.bounded_analytic64_certificate_count_def;
val bounded_analytic_program_plan_check_v =
  translate
    compute_boundedAnalyticPlanCVTheory.bounded_analytic_program_plan_check_def;
val bounded_analytic_source_plan_check_v =
  translate
    compute_boundedAnalyticPlanCVTheory.bounded_analytic_source_plan_check_def;

val _ = export_theory ();
