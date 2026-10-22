(* CakeML translation of the prepared outer analytic executor. *)
Theory compute_boundedAnalyticProgramProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorProgramProg compute_boundedAnalyticProgram

val _ = translation_extends "compute_boundedTaylorProgramProg";

val _ = register_type ``:bounded_analytic64_instruction``;
val _ = register_type ``:bounded_analytic64_certificate``;

val bounded_analytic64_program_step_v =
  translate
    compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def;
val bounded_analytic64_program_run_v =
  translate
    compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def;
val bounded_analytic64_program_eval_v =
  translate
    compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_def;

val _ = export_theory ();
