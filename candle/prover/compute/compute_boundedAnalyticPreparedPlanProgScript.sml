(* CakeML translation of generic bounded analytic source preparation. *)
Theory compute_boundedAnalyticPreparedPlanProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedPackedAnalyticCheckProg
  compute_boundedAnalyticPreparedPlan

val _ = translation_extends "compute_boundedPackedAnalyticCheckProg";

val bounded_analytic_scale40_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_scale40_def;
val bounded_analytic_nat_ceil_div_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_nat_ceil_div_def;
val bounded_analytic_rational_constant64_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_rational_constant64_def;
val bounded_analytic_compile_poly_instruction_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_poly_instruction_def;
val bounded_analytic_compile_poly_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_poly_def;
val bounded_analytic_compile_instruction_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_instruction_def;
val bounded_analytic_recognized_specialization_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_recognized_specialization_def;
val bounded_analytic_compile_specialized_instruction_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_specialized_instruction_def;
val bounded_analytic_compile_program_v =
  translate
    compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_program_def;

val _ = export_theory ();
