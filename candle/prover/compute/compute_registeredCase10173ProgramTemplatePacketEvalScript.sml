(*****************************************************************************
 * Exact ordinary-program templates for the authenticated case-10173 source.
 *
 * The source program has six packet-dependent square-root certificates in
 * its 31-instruction prefix.  The historical eight-instruction block is
 * replaced by opcode 9, and the remaining 15 instructions are fixed.  This
 * layer exposes those literal instruction sequences so the ordinary prefix
 * and suffix can be refined without reopening program preparation.
 *****************************************************************************)
Theory compute_registeredCase10173ProgramTemplatePacketEval
Ancestors
  compute_registeredCase10173ProgramSplitPacketEval
Libs
  bossLib preamble

Definition registered_case10173_cv_of_list_def:
  registered_case10173_cv_of_list [] = Num 0 /\
  registered_case10173_cv_of_list (item::items) =
    Pair item (registered_case10173_cv_of_list items)
End

Definition registered_case10173_source_prefix_template_def:
  registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5 =
    registered_case10173_cv_of_list
      [Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 1277) (Num 0)) (Num 999)))
             (Pair (Num 4) (Num 0))));
       Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0));
       Pair (Num 1) center0;
       Pair (Num 0)
         (Pair (Pair (Num 0)
           (Pair (Pair (Num 136649) (Num 0)) (Num 499999)))
           (Num 0));
       Num 4;
       Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 136649) (Num 0)) (Num 499999)))
             (Pair (Pair (Num 0)
               (Pair (Pair (Num 109) (Num 0)) (Num 49)))
               (Pair (Num 2) (Pair (Num 4) (Pair (Num 4) (Num 0)))))));
       Pair (Num 0) (Pair (Pair (Num 1) (Num 1)) (Num 0));
       Pair (Num 1) center1;
       Pair (Num 0)
         (Pair (Pair (Num 0)
           (Pair (Pair (Num 273853) (Num 0)) (Num 999999)))
           (Pair (Num 2) (Num 0)));
       Num 4;
       Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 273853) (Num 0)) (Num 999999)))
             (Pair (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
               (Pair (Num 4) (Pair (Num 4) (Num 0))))));
       Pair (Num 0) (Pair (Pair (Num 1) (Num 2)) (Num 0));
       Pair (Num 1) center2;
       Pair (Num 0)
         (Pair (Pair (Num 0)
           (Pair (Pair (Num 273853) (Num 0)) (Num 999999)))
           (Pair (Num 2) (Num 0)));
       Num 4;
       Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 273853) (Num 0)) (Num 999999)))
             (Pair (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
               (Pair (Num 4) (Pair (Num 4) (Num 0))))));
       Pair (Num 0) (Pair (Pair (Num 1) (Num 3)) (Num 0));
       Pair (Num 1) center3;
       Pair (Num 0)
         (Pair (Pair (Num 0)
           (Pair (Pair (Num 354409) (Num 0)) (Num 499999)))
           (Num 0));
       Num 4;
       Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 354409) (Num 0)) (Num 499999)))
             (Pair (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
               (Pair (Num 2)
                 (Pair (Num 4) (Pair (Num 4) (Num 0)))))));
       Pair (Num 0) (Pair (Pair (Num 1) (Num 4)) (Num 0));
       Pair (Num 1) center4;
       Pair (Num 0)
         (Pair (Pair (Num 0)
           (Pair (Pair (Num 78497) (Num 0)) (Num 249999)))
           (Pair (Num 2) (Num 0)));
       Num 4;
       Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 78497) (Num 0)) (Num 249999)))
             (Pair (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
               (Pair (Num 4) (Pair (Num 4) (Num 0))))));
       Pair (Num 0) (Pair (Pair (Num 1) (Num 5)) (Num 0));
       Pair (Num 1) center5;
       Pair (Num 0)
         (Pair (Pair (Num 0)
           (Pair (Pair (Num 78497) (Num 0)) (Num 249999)))
           (Pair (Num 2) (Num 0)));
       Num 4;
       Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
           (Pair (Pair (Num 0)
             (Pair (Pair (Num 78497) (Num 0)) (Num 249999)))
             (Pair (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
               (Pair (Num 4) (Pair (Num 4) (Num 0))))))]
End

Definition registered_case10173_source_suffix_template_def:
  registered_case10173_source_suffix_template =
    registered_case10173_cv_of_list
      [Pair (Num 0)
         (Pair (Pair (Num 0) (Pair (Pair (Num 0) (Num 1)) (Num 0)))
           (Num 0));
       Num 4;
       Num 3;Num 3;Num 3;Num 3;Num 3;Num 3;Num 3;
       Num 3;Num 3;Num 3;Num 3;Num 3;Num 3]
End

Theorem registered_case10173_source_prefix_template_length:
  registered_case10173_cv_list_length
    (registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5) = 31
Proof
  EVAL_TAC
QED

Theorem registered_case10173_source_suffix_template_length:
  registered_case10173_cv_list_length
    registered_case10173_source_suffix_template = 15
Proof
  EVAL_TAC
QED

Theorem registered_case10173_prepared_source_program_templates:
  let sqrt_data = registered_case10173_cv_of_list
    [certificate0;certificate1;certificate2;certificate3;
     certificate4;certificate5;certificate6] in
  let patched_program =
    registered_case10173_patch_program
      (registered_case10173_analytic_program_patch_sqrt_cv sqrt_data
        registered_case10173_genuine_source_program) in
  let spliced_program =
    registered_case10173_hist_splice_cv 31 patched_program in
    registered_case10173_cv_take 31 spliced_program =
      registered_case10173_source_prefix_template
        certificate0 certificate1 certificate2 certificate3
        certificate4 certificate5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 spliced_program) =
        Pair (Num 9) (Num 0) /\
    registered_case10173_cv_drop 32 spliced_program =
      registered_case10173_source_suffix_template
Proof
  simp
    [registered_case10173_cv_of_list_def,
     registered_case10173_source_prefix_template_def,
     registered_case10173_source_suffix_template_def,
     compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_patch_program_def,
     compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_source_program_def,
     compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_def,
     compute_registeredCase10173AnalyticSqrtEvalTheory.registered_case10173_analytic_instruction_patch_sqrt_cv_def,
     compute_registeredCase10173AnalyticSqrtEvalTheory.registered_case10173_analytic_instruction_is_sqrt_cv_def,
     compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
     compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def,
     compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_take_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
