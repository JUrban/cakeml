(*****************************************************************************
 * Arbitrary-state joint trace for the final specialized case-16594 pair.
 *
 * Positions 120 and 121 are respectively -d(delta)/dx_5 and 4*x_2*delta.
 * This is the final reusable specialized splice for the arbitrary accepted-
 * cell trace.  It preserves the word, semantic, packet, and runtime-stack
 * invariants without depending on any concrete cell fixture.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointThirdSpecializedPairInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointSecondSpecializedPairInvariant
  compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source120_decode_and_refines_general:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source120_cv =
      SOME (EL 120 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 120 bounded_case16594_program)
    (BoundedAnalytic64NegDeltaDerivative 5)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source120_cv_def]
      >> irule
           compute_boundedCase16594ObjectDispatchJointFirstSpecializedPairInvariantTheory.bounded_case16594_object_cv_nth_decodes_general
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source120_specialization_ok]
QED

Theorem bounded_case16594_object_source121_decode_and_refines_general:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source121_cv =
      SOME (EL 121 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 121 bounded_case16594_program)
    (BoundedAnalytic64FourCoordinateDelta 2)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source121_cv_def]
      >> irule
           compute_boundedCase16594ObjectDispatchJointFirstSpecializedPairInvariantTheory.bounded_case16594_object_cv_nth_decodes_general
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source121_specialization_ok]
QED

Theorem bounded_case16594_object_joint_third_specialized_pair_trace:
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LENGTH semantic_center_boxes = 6 /\
  LENGTH semantic_outer_boxes = 6 /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_runtime_certificate_trace semantic_radii
    word_center_boxes word_outer_boxes
    (BoundedAnalytic64NegDeltaDerivative 5 ::
     BoundedAnalytic64FourCoordinateDelta 2 :: prepared_suffix)
    word_state = SOME (final_word_state,packets) /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  bounded_case16594_word_dispatch_packet_contracts
    (SND word_state) packets /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state)
  ==>
  ?word_after_pair packets_after_pair semantic_after_pair
   runtime_stack_after_pair.
    bounded_analytic64_program_runtime_certificate_trace semantic_radii
      word_center_boxes word_outer_boxes prepared_suffix word_after_pair =
        SOME (final_word_state,packets_after_pair) /\
    bounded_analytic64_state_covers_object_q
      word_after_pair semantic_after_pair /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after_pair) packets_after_pair /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      [EL 120 bounded_case16594_program;EL 121 bounded_case16594_program]
      [BoundedAnalytic64NegDeltaDerivative 5;
       BoundedAnalytic64FourCoordinateDelta 2]
      (Pair (Num 6) (Pair (Num 3) (Num 0)))
      (Pair bounded_case16594_object_source120_cv
        (Pair bounded_case16594_object_source121_cv (Num 0)))
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packets))
      runtime_stack semantic_state
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after_pair)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after_pair))))
      semantic_after_pair
Proof
  strip_tac
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet120`
         (qx_choose_then `word_after120`
           (qx_choose_then `packets_after120` strip_assume_tac)))
  >> `packet120 = [] /\ SND word_after120 = SND word_state` by
       metis_tac
         [compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_neg5_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_neg_derivative semantic_radii word_center_boxes 5 =
          SOME word_result` by
       (Cases_on `word_state`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_neg_refinement_context
        semantic_radii weights semantic_center_boxes 5` by
       (irule
          compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_delta_neg_refinement_context_from_word
        >> simp []
        >> metis_tac [])
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_radii` |-> `runtime_radii`,
          `word_state` |-> `word_state`,
          `semantic_state` |-> `semantic_state`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `word_next` |-> `word_after120`,
          `packet_rest` |-> `packets`,
          `runtime_stack` |-> `runtime_stack`]
         compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_neg5_runtime_step)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `semantic_after120`
         (qx_choose_then `runtime_stack_after120` strip_assume_tac))
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet121`
         (qx_choose_then `word_after121`
           (qx_choose_then `packets_after121` strip_assume_tac)))
  >> `packet121 = [] /\ SND word_after121 = SND word_after120` by
       metis_tac
         [compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_product2_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_four_coordinate semantic_radii word_center_boxes
          word_outer_boxes 2 = SOME word_result` by
       (Cases_on `word_after120`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_product_refinement_context
        semantic_radii weights semantic_center_boxes semantic_outer_boxes 2` by
       (irule
          compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_delta_product_refinement_context_from_word
        >> simp []
        >> metis_tac [])
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_radii` |-> `runtime_radii`,
          `word_state` |-> `word_after120`,
          `semantic_state` |-> `semantic_after120`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `word_next` |-> `word_after121`,
          `packet_rest` |-> `packets`,
          `runtime_stack` |-> `runtime_stack_after120`]
         compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_product2_runtime_step)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `semantic_after121`
         (qx_choose_then `runtime_stack_after121` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        [EL 120 bounded_case16594_program;EL 121 bounded_case16594_program]
        [BoundedAnalytic64NegDeltaDerivative 5;
         BoundedAnalytic64FourCoordinateDelta 2]
        (Pair (Num 6) (Pair (Num 3) (Num 0)))
        (Pair bounded_case16594_object_source120_cv
          (Pair bounded_case16594_object_source121_cv (Num 0)))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after121)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets))))
        semantic_after121` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source120_decode_and_refines_general,
           bounded_case16594_object_source121_decode_and_refines_general]
        >> metis_tac [])
  >> qexists_tac `word_after121`
  >> qexists_tac `packets`
  >> qexists_tac `semantic_after121`
  >> qexists_tac `runtime_stack_after121`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
