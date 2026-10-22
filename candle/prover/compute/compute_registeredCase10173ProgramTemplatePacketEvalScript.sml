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

Theorem registered_case10173_zero_terminated_cv_list_representation:
  !items.
    registered_case10173_cv_list_zero_terminated items ==>
    ?values.
      items = registered_case10173_cv_of_list values /\
      LENGTH values = registered_case10173_cv_list_length items
Proof
  ho_match_mp_tac compute_execTheory.cv_induction
  >> conj_tac
  >- rw
       [compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_cv_list_zero_terminated_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
        registered_case10173_cv_of_list_def]
  >> rpt gen_tac
  >> strip_tac
  >> rw
       [compute_registeredCase10173ProgramShapePacketEvalTheory.registered_case10173_cv_list_zero_terminated_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> res_tac
  >> qexists_tac `items::values`
  >> simp [registered_case10173_cv_of_list_def]
QED

Theorem registered_case10173_zero_terminated_cv_list_seven:
  registered_case10173_cv_list_zero_terminated items /\
  registered_case10173_cv_list_length items = 7 ==>
  ?item0 item1 item2 item3 item4 item5 item6.
    items = registered_case10173_cv_of_list
      [item0;item1;item2;item3;item4;item5;item6]
Proof
  strip_tac
  >> drule registered_case10173_zero_terminated_cv_list_representation
  >> strip_tac
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> metis_tac []
QED

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

Theorem registered_case10173_prepared_source_program_templates_from_patch:
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
      (registered_case10173_hist_splice_cv 31 patched_program) =
        registered_case10173_source_prefix_template
          certificate0 certificate1 certificate2 certificate3
          certificate4 certificate5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31
        (registered_case10173_hist_splice_cv 31 patched_program)) =
          Pair (Num 9) (Num 0) /\
    registered_case10173_cv_drop 32
      (registered_case10173_hist_splice_cv 31 patched_program) =
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
           registered_case10173_prepared_source_program_templates))
QED

Theorem registered_case10173_authenticated_source_program_templates:
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
      (registered_case10173_hist_splice_cv 31 box_program) =
        registered_case10173_source_prefix_template
          box0 box1 box2 box3 box4 box5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31
        (registered_case10173_hist_splice_cv 31 box_program)) =
          Pair (Num 9) (Num 0) /\
    registered_case10173_cv_drop 32
      (registered_case10173_hist_splice_cv 31 box_program) =
        registered_case10173_source_suffix_template /\
    registered_case10173_cv_take 31
      (registered_case10173_hist_splice_cv 31 center_program) =
        registered_case10173_source_prefix_template
          center0 center1 center2 center3 center4 center5 /\
    registered_case10173_cv_take 1
      (registered_case10173_cv_drop 31
        (registered_case10173_hist_splice_cv 31 center_program)) =
          Pair (Num 9) (Num 0) /\
    registered_case10173_cv_drop 32
      (registered_case10173_hist_splice_cv 31 center_program) =
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
  >> imp_res_tac registered_case10173_prepared_source_program_templates_from_patch
  >> metis_tac []
QED

val _ = export_theory ();
