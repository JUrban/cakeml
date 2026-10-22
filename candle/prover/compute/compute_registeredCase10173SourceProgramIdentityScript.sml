(*****************************************************************************
 * Exact identity of a prepared case-10173 source program.
 *
 * The trace evaluator consumes a literal prefix/opcode-9/suffix program.
 * This layer proves that the program produced by the authenticated source
 * patcher and splice operation is exactly that value, rather than merely
 * agreeing with three independently inspected slices.
 *****************************************************************************)
Theory compute_registeredCase10173SourceProgramIdentity
Ancestors
  compute_registeredCase10173ProgramTemplatePacketEval
Libs
  bossLib preamble

Theorem registered_case10173_prepared_source_program_exact:
  let sqrt_data = registered_case10173_cv_of_list
    [certificate0;certificate1;certificate2;certificate3;
     certificate4;certificate5;certificate6] in
  let patched_program =
    registered_case10173_patch_program
      (registered_case10173_analytic_program_patch_sqrt_cv sqrt_data
        registered_case10173_genuine_source_program) in
  registered_case10173_hist_splice_cv 31 patched_program =
    registered_case10173_cv_append
      (registered_case10173_source_prefix_template
        certificate0 certificate1 certificate2 certificate3
        certificate4 certificate5)
      (Pair (Num 9) registered_case10173_source_suffix_template)
Proof
  simp
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
     compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_prefix_template_def,
     compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_suffix_template_def,
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
     compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_prepared_source_program_exact_from_patch:
  registered_case10173_cv_list_zero_terminated sqrt_data /\
  registered_case10173_cv_list_length sqrt_data = 7 /\
  registered_case10173_analytic_program_patch_sqrt_cv sqrt_data
      registered_case10173_genuine_source_program =
    Pair (Num 0) patched_program ==>
  ?certificate0 certificate1 certificate2 certificate3
   certificate4 certificate5 certificate6.
    sqrt_data = registered_case10173_cv_of_list
      [certificate0;certificate1;certificate2;certificate3;
       certificate4;certificate5;certificate6] /\
    registered_case10173_hist_splice_cv 31 patched_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          certificate0 certificate1 certificate2 certificate3
          certificate4 certificate5)
        (Pair (Num 9) registered_case10173_source_suffix_template)
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_zero_terminated_cv_list_seven
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexists_tac `item0`
  >> qexists_tac `item1`
  >> qexists_tac `item2`
  >> qexists_tac `item3`
  >> qexists_tac `item4`
  >> qexists_tac `item5`
  >> qexists_tac `item6`
  >> conj_tac >- asm_rewrite_tac []
  >> rveq
  >> `registered_case10173_patch_program
        (registered_case10173_analytic_program_patch_sqrt_cv
          (registered_case10173_cv_of_list
            [item0;item1;item2;item3;item4;item5;item6])
          registered_case10173_genuine_source_program) = patched_program` by
       asm_simp_tac std_ss
         [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_patch_program_def]
  >> rveq
  >> ACCEPT_TAC
       (SIMP_RULE std_ss [LET_THM]
         (INST
           [``certificate0:cv`` |-> ``item0:cv``,
            ``certificate1:cv`` |-> ``item1:cv``,
            ``certificate2:cv`` |-> ``item2:cv``,
            ``certificate3:cv`` |-> ``item3:cv``,
            ``certificate4:cv`` |-> ``item4:cv``,
            ``certificate5:cv`` |-> ``item5:cv``,
            ``certificate6:cv`` |-> ``item6:cv``]
           registered_case10173_prepared_source_program_exact))
QED

val _ = export_theory ();
