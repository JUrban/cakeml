(* CakeML translation of the prepared compact Taylor postfix executor. *)
Theory compute_boundedTaylorProgramProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedDeltaTaylorProg compute_boundedTaylorProgram

val _ = translation_extends "compute_boundedDeltaTaylorProg";

val _ = register_type ``:bounded_taylor64_instruction``;

val bounded_taylor64_stack_well_formed_v =
  translate
    compute_boundedTaylorProgramTheory.bounded_taylor64_stack_well_formed_def;
val bounded_taylor64_neg_complete_v =
  translate
    compute_boundedTaylorProgramTheory.bounded_taylor64_neg_complete_def;
val bounded_taylor64_add_complete_v =
  translate
    compute_boundedTaylorProgramTheory.bounded_taylor64_add_complete_def;
val bounded_taylor64_program_step_v =
  translate
    compute_boundedTaylorProgramTheory.bounded_taylor64_program_step_def;
val bounded_taylor64_program_run_v =
  translate
    compute_boundedTaylorProgramTheory.bounded_taylor64_program_run_def;
val bounded_taylor64_program_eval_v =
  translate
    compute_boundedTaylorProgramTheory.bounded_taylor64_program_eval_def;

val _ = export_theory ();
