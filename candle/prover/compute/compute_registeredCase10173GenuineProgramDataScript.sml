(*****************************************************************************
 * Exact program data for the first authenticated case-10173 job.
 *
 * The source program and both square-root certificate streams are projected
 * from the registered checked call itself.  The pure patch/splice functions
 * mirror the registered source preparation and expose compact program values
 * for the subsequent memoized program-run proof.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineProgramData
Ancestors
  compute_registeredCase10173GenuineHistStepEval
Libs
  bossLib preamble

Definition registered_case10173_genuine_source_program_def:
  registered_case10173_genuine_source_program =
    case registered_case10173_historical_chunk16_cexp of
    | App function_name [source_expression;jobs_expression;roots_expression] =>
        (case compute_exp_to_cv source_expression of
         | SOME source_program => source_program
         | NONE => Num 0)
    | _ => Num 0
End

Definition registered_case10173_first_job_box_sqrt_data_def:
  registered_case10173_first_job_box_sqrt_data =
    case bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp of
    | SOME
        (Pair
          (Pair box_sqrt_data (Pair center_sqrt_data boxes))
          root_record) => box_sqrt_data
    | _ => Num 0
End

Definition registered_case10173_first_job_center_sqrt_data_def:
  registered_case10173_first_job_center_sqrt_data =
    case bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp of
    | SOME
        (Pair
          (Pair box_sqrt_data (Pair center_sqrt_data boxes))
          root_record) => center_sqrt_data
    | _ => Num 0
End

Definition registered_case10173_genuine_box_patch_def:
  registered_case10173_genuine_box_patch =
    registered_case10173_analytic_program_patch_sqrt_cv
      registered_case10173_first_job_box_sqrt_data
      registered_case10173_genuine_source_program
End

Definition registered_case10173_genuine_center_patch_def:
  registered_case10173_genuine_center_patch =
    registered_case10173_analytic_program_patch_sqrt_cv
      registered_case10173_first_job_center_sqrt_data
      registered_case10173_genuine_source_program
End

Definition registered_case10173_patch_remainder_def:
  registered_case10173_patch_remainder (Pair remainder program : cv) =
    remainder /\
  registered_case10173_patch_remainder (Num n) = Num n
End

Definition registered_case10173_patch_program_def:
  registered_case10173_patch_program (Pair remainder program : cv) =
    program /\
  registered_case10173_patch_program (Num n) = Num n
End

Definition registered_case10173_genuine_box_program_def:
  registered_case10173_genuine_box_program =
    registered_case10173_patch_program
      registered_case10173_genuine_box_patch
End

Definition registered_case10173_genuine_center_program_def:
  registered_case10173_genuine_center_program =
    registered_case10173_patch_program
      registered_case10173_genuine_center_patch
End

Definition registered_case10173_cv_drop_def:
  registered_case10173_cv_drop 0 program = program /\
  registered_case10173_cv_drop (SUC count) (Pair instruction program) =
    registered_case10173_cv_drop count program /\
  registered_case10173_cv_drop (SUC count) (Num n) = Num n
End

Definition registered_case10173_hist_splice_cv_def:
  registered_case10173_hist_splice_cv 0 program =
    Pair (Num 9) (registered_case10173_cv_drop 8 program) /\
  registered_case10173_hist_splice_cv (SUC count)
      (Pair instruction program) =
    Pair instruction
      (registered_case10173_hist_splice_cv count program) /\
  registered_case10173_hist_splice_cv (SUC count) (Num n) = Num n
End

Definition registered_case10173_genuine_spliced_box_program_def:
  registered_case10173_genuine_spliced_box_program =
    registered_case10173_hist_splice_cv 31
      registered_case10173_genuine_box_program
End

Definition registered_case10173_genuine_spliced_center_program_def:
  registered_case10173_genuine_spliced_center_program =
    registered_case10173_hist_splice_cv 31
      registered_case10173_genuine_center_program
End

Definition registered_case10173_cv_list_length_def:
  registered_case10173_cv_list_length (Num n : cv) = 0 /\
  registered_case10173_cv_list_length (Pair item items) =
    SUC (registered_case10173_cv_list_length items)
End

Theorem registered_case10173_genuine_program_data_shape:
  registered_case10173_cv_list_length
      registered_case10173_genuine_source_program = 54 /\
  registered_case10173_patch_remainder
      registered_case10173_genuine_box_patch = Num 0 /\
  registered_case10173_patch_remainder
      registered_case10173_genuine_center_patch = Num 0 /\
  registered_case10173_cv_list_length
      registered_case10173_genuine_box_program = 54 /\
  registered_case10173_cv_list_length
      registered_case10173_genuine_center_program = 54 /\
  registered_case10173_cv_list_length
      registered_case10173_genuine_spliced_box_program = 47 /\
  registered_case10173_cv_list_length
      registered_case10173_genuine_spliced_center_program = 47
Proof
  simp
    [registered_case10173_genuine_source_program_def,
     registered_case10173_first_job_box_sqrt_data_def,
     registered_case10173_first_job_center_sqrt_data_def,
     registered_case10173_genuine_box_patch_def,
     registered_case10173_genuine_center_patch_def,
     registered_case10173_patch_remainder_def,
     registered_case10173_genuine_box_program_def,
     registered_case10173_genuine_center_program_def,
     registered_case10173_genuine_spliced_box_program_def,
     registered_case10173_genuine_spliced_center_program_def,
     compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_def,
     compute_registeredCase10173AnalyticSqrtEvalTheory.registered_case10173_analytic_instruction_patch_sqrt_cv_def,
     compute_registeredCase10173AnalyticSqrtEvalTheory.registered_case10173_analytic_instruction_is_sqrt_cv_def,
     registered_case10173_hist_splice_cv_def,
     registered_case10173_cv_drop_def,
     registered_case10173_cv_list_length_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
