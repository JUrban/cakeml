(*****************************************************************************
 * Authenticated case-10173 source-program templates in the corrected tag-10
 * private-opcode environment.  The source preparation is unchanged; only the
 * splice marker is reassembled at its current registered opcode.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10ProgramTemplateExactEval
Ancestors
  compute_registeredCase10173ProgramTemplateExactEval
  compute_registeredCase10173ProgramTemplatePacketEval
  compute_registeredCase10173Tag10GenuineProgramMemoEval
Libs
  bossLib preamble

Theorem registered_case10173_tag10_prepared_source_program_templates:
  let sqrt_data = registered_case10173_cv_of_list
    [certificate0;certificate1;certificate2;certificate3;
     certificate4;certificate5;certificate6] in
  let patched_program =
    registered_case10173_patch_program
      (registered_case10173_analytic_program_patch_sqrt_cv sqrt_data
        registered_case10173_genuine_source_program) in
  let spliced_program =
    registered_case10173_tag10_hist_splice_cv 31 patched_program in
    registered_case10173_cv_take 31 spliced_program =
      registered_case10173_source_prefix_template
        certificate0 certificate1 certificate2 certificate3
        certificate4 certificate5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 spliced_program) =
        Pair (Num 10) (Num 0) /\
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
     compute_registeredCase10173Tag10GenuineProgramMemoEvalTheory.registered_case10173_tag10_hist_splice_cv_def,
     compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_drop_def,
     compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_take_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_tag10_prepared_source_program_templates_from_patch:
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
    registered_case10173_cv_take 31
      (registered_case10173_tag10_hist_splice_cv 31 patched_program) =
        registered_case10173_source_prefix_template
          certificate0 certificate1 certificate2 certificate3
          certificate4 certificate5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31
        (registered_case10173_tag10_hist_splice_cv 31 patched_program)) =
          Pair (Num 10) (Num 0) /\
    registered_case10173_cv_drop 32
      (registered_case10173_tag10_hist_splice_cv 31 patched_program) =
        registered_case10173_source_suffix_template
Proof
  strip_tac
  >> drule registered_case10173_zero_terminated_cv_list_seven
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
           registered_case10173_tag10_prepared_source_program_templates))
QED

Theorem registered_case10173_tag10_authenticated_source_program_templates:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record ==>
  ?box_sqrt_data center_sqrt_data boxes box_program center_program
   box0 box1 box2 box3 box4 box5 box6
   center0 center1 center2 center3 center4 center5 center6.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
    box_sqrt_data = registered_case10173_cv_of_list
      [box0;box1;box2;box3;box4;box5;box6] /\
    center_sqrt_data = registered_case10173_cv_of_list
      [center0;center1;center2;center3;center4;center5;center6] /\
    registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) box_program /\
    registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) center_program /\
    registered_case10173_cv_take 31
      (registered_case10173_tag10_hist_splice_cv 31 box_program) =
        registered_case10173_source_prefix_template
          box0 box1 box2 box3 box4 box5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31
        (registered_case10173_tag10_hist_splice_cv 31 box_program)) =
          Pair (Num 10) (Num 0) /\
    registered_case10173_cv_drop 32
      (registered_case10173_tag10_hist_splice_cv 31 box_program) =
        registered_case10173_source_suffix_template /\
    registered_case10173_cv_take 31
      (registered_case10173_tag10_hist_splice_cv 31 center_program) =
        registered_case10173_source_prefix_template
          center0 center1 center2 center3 center4 center5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31
        (registered_case10173_tag10_hist_splice_cv 31 center_program)) =
          Pair (Num 10) (Num 0) /\
    registered_case10173_cv_drop 32
      (registered_case10173_tag10_hist_splice_cv 31 center_program) =
        registered_case10173_source_suffix_template
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_authenticated_source_program_shape
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_binding_components
  >> imp_res_tac
       compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_positive_q_interval_list_zero_terminated
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_packet_sqrt_root_lengths
  >> imp_res_tac
       compute_registeredCase10173ProgramPreparationPacketEvalTheory.registered_case10173_positive_q_interval_list_length
  >> gvs [compute_execTheory.cv_11]
  >> subgoal
       `registered_case10173_cv_list_zero_terminated box_sqrt_data /\
        registered_case10173_cv_list_length box_sqrt_data = 7 /\
        registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
          registered_case10173_genuine_source_program =
            Pair (Num 0) box_program`
  >- simp []
  >> subgoal
       `registered_case10173_cv_list_zero_terminated center_sqrt_data /\
        registered_case10173_cv_list_length center_sqrt_data = 7 /\
        registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
          registered_case10173_genuine_source_program =
            Pair (Num 0) center_program`
  >- simp []
  >> imp_res_tac registered_case10173_tag10_prepared_source_program_templates_from_patch
  >> metis_tac []
QED

Theorem registered_case10173_tag10_program_from_template_fragments:
  registered_case10173_cv_list_length program = 47 /\
  registered_case10173_cv_take 31 program = prefix /\
  registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31 program) = Pair (Num 10) (Num 0) /\
  registered_case10173_cv_drop 32 program = suffix ==>
  program =
    registered_case10173_cv_append prefix (Pair (Num 10) suffix)
Proof
  strip_tac
  >> subgoal
       `registered_case10173_cv_drop 1
          (registered_case10173_cv_drop 31 program) = suffix`
  >- (once_rewrite_tac
        [GSYM
          (Q.SPECL [`31`,`1`,`program`]
            compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_drop_add)]
      >> simp [])
  >> subgoal
       `registered_case10173_cv_drop 31 program = Pair (Num 10) suffix`
  >- (mp_tac
        (Q.SPECL
          [`1`,`registered_case10173_cv_drop 31 program`]
          compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_take_drop)
      >> impl_tac
      >- (mp_tac
            (Q.SPECL [`31`,`program`]
              compute_registeredCase10173ProgramSplicePacketEvalTheory.registered_case10173_cv_drop_length)
          >> simp [])
      >> simp
           [compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_def])
  >> mp_tac
       (Q.SPECL [`31`,`program`]
         compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_take_drop)
  >> impl_tac >- simp []
  >> metis_tac []
QED

Theorem registered_case10173_tag10_prepared_program_splice_length:
  registered_case10173_cv_list_length program = 54 ==>
  registered_case10173_cv_list_length
    (registered_case10173_tag10_hist_splice_cv 31 program) = 47
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173Tag10GenuineProgramMemoEvalTheory.registered_case10173_tag10_hist_splice_length]
  >> irule
       compute_registeredCase10173ProgramSplicePacketEvalTheory.registered_case10173_prepared_program_splice_length
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_tag10_authenticated_source_programs_exact:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record ==>
  ?box_sqrt_data center_sqrt_data boxes box_program center_program
   box0 box1 box2 box3 box4 box5 box6
   center0 center1 center2 center3 center4 center5 center6.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
    box_sqrt_data = registered_case10173_cv_of_list
      [box0;box1;box2;box3;box4;box5;box6] /\
    center_sqrt_data = registered_case10173_cv_of_list
      [center0;center1;center2;center3;center4;center5;center6] /\
    registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) box_program /\
    registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
      registered_case10173_genuine_source_program =
        Pair (Num 0) center_program /\
    registered_case10173_tag10_hist_splice_cv 31 box_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          box0 box1 box2 box3 box4 box5)
        (Pair (Num 10) registered_case10173_source_suffix_template) /\
    registered_case10173_tag10_hist_splice_cv 31 center_program =
      registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          center0 center1 center2 center3 center4 center5)
        (Pair (Num 10) registered_case10173_source_suffix_template) /\
    registered_case10173_cv_list_length box_program = 54 /\
    registered_case10173_cv_list_length center_program = 54
Proof
  strip_tac
  >> drule
       registered_case10173_tag10_authenticated_source_program_templates
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> drule
       compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_authenticated_source_program_shape
  >> simp []
  >> disch_then (qspecl_then [`root_record`,`object_job`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> gvs []
  >> imp_res_tac
       registered_case10173_tag10_prepared_program_splice_length
  >> imp_res_tac registered_case10173_tag10_program_from_template_fragments
  >> metis_tac []
QED

val _ = export_theory ();
