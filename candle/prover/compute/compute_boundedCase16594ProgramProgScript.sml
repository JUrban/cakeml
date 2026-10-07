(*
  CakeML translation of the pinned 167-instruction case16594 analytic plan.
  The executable stack validator rejects malformed polynomial/analytic plans;
  semantic authorization of the six delta specializations remains a separate
  proof obligation before this DEVELOPMENT fixture can support a release.
*)
Theory compute_boundedCase16594ProgramProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedCase16594InputProg compute_boundedCase16594ProgramData

val _ = translation_extends "compute_boundedCase16594InputProg";

val _ = register_type ``:bounded_poly_instruction``;
val _ = register_type ``:bounded_analytic_instruction``;
val _ = register_type ``:bounded_analytic_specialization``;

val bounded_case16594_program_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_case16594_program_def;
val bounded_case16594_specializations_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_case16594_specializations_def;
val bounded_poly_stack_step_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_poly_stack_step_def;
val bounded_poly_stack_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_poly_stack_def;
val bounded_poly_program_ok_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_poly_program_ok_def;
val bounded_analytic_stack_step_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_stack_step_def;
val bounded_analytic_stack_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_stack_def;
val bounded_analytic_specialization_program_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_program_def;
val bounded_analytic_specialization_ok_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specialization_ok_def;
val bounded_analytic_specializations_ok_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_analytic_specializations_ok_def;
val bounded_case16594_program_ok_v =
  translate
    compute_boundedCase16594ProgramDataTheory.bounded_case16594_program_ok_def;

val _ = export_theory ();
