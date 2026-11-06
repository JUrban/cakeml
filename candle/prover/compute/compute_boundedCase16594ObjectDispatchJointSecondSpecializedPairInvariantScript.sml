(*****************************************************************************
 * Arbitrary-state joint trace for the second specialized case-16594 pair.
 *
 * Positions 77 and 78 are respectively -d(delta)/dx_4 and 4*x_1*delta.
 * This is the second reusable specialized splice for the arbitrary accepted-
 * cell trace.  It preserves the word, semantic, packet, and runtime-stack
 * invariants without depending on any concrete cell fixture.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointSecondSpecializedPairInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointFirstSpecializedPairInvariant
  compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source77_decode_and_refines_general:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source77_cv =
      SOME (EL 77 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 77 bounded_case16594_program)
    (BoundedAnalytic64NegDeltaDerivative 4)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source77_cv_def]
      >> irule bounded_case16594_object_cv_nth_decodes_general
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source77_specialization_ok]
QED

Theorem bounded_case16594_object_source78_decode_and_refines_general:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source78_cv =
      SOME (EL 78 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 78 bounded_case16594_program)
    (BoundedAnalytic64FourCoordinateDelta 1)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source78_cv_def]
      >> irule bounded_case16594_object_cv_nth_decodes_general
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source78_specialization_ok]
QED

Theorem bounded_case16594_object_joint_second_specialized_pair_trace:
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
    (BoundedAnalytic64NegDeltaDerivative 4 ::
     BoundedAnalytic64FourCoordinateDelta 1 :: prepared_suffix)
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
      [EL 77 bounded_case16594_program;EL 78 bounded_case16594_program]
      [BoundedAnalytic64NegDeltaDerivative 4;
       BoundedAnalytic64FourCoordinateDelta 1]
      (Pair (Num 5) (Pair (Num 2) (Num 0)))
      (Pair bounded_case16594_object_source77_cv
        (Pair bounded_case16594_object_source78_cv (Num 0)))
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
       (qx_choose_then `packet77`
         (qx_choose_then `word_after77`
           (qx_choose_then `packets_after77` strip_assume_tac)))
  >> `packet77 = [] /\ SND word_after77 = SND word_state` by
       metis_tac
         [compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_neg4_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_neg_derivative semantic_radii word_center_boxes 4 =
          SOME word_result` by
       (Cases_on `word_state`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_neg_refinement_context
        semantic_radii weights semantic_center_boxes 4` by
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
          `word_next` |-> `word_after77`,
          `packet_rest` |-> `packets`,
          `runtime_stack` |-> `runtime_stack`]
         compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_neg4_runtime_step)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `semantic_after77`
         (qx_choose_then `runtime_stack_after77` strip_assume_tac))
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet78`
         (qx_choose_then `word_after78`
           (qx_choose_then `packets_after78` strip_assume_tac)))
  >> `packet78 = [] /\ SND word_after78 = SND word_after77` by
       metis_tac
         [compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_product1_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_four_coordinate semantic_radii word_center_boxes
          word_outer_boxes 1 = SOME word_result` by
       (Cases_on `word_after77`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_product_refinement_context
        semantic_radii weights semantic_center_boxes semantic_outer_boxes 1` by
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
          `word_state` |-> `word_after77`,
          `semantic_state` |-> `semantic_after77`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `word_next` |-> `word_after78`,
          `packet_rest` |-> `packets`,
          `runtime_stack` |-> `runtime_stack_after77`]
         compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_product1_runtime_step)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `semantic_after78`
         (qx_choose_then `runtime_stack_after78` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        [EL 77 bounded_case16594_program;EL 78 bounded_case16594_program]
        [BoundedAnalytic64NegDeltaDerivative 4;
         BoundedAnalytic64FourCoordinateDelta 1]
        (Pair (Num 5) (Pair (Num 2) (Num 0)))
        (Pair bounded_case16594_object_source77_cv
          (Pair bounded_case16594_object_source78_cv (Num 0)))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after78)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets))))
        semantic_after78` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source77_decode_and_refines_general,
           bounded_case16594_object_source78_decode_and_refines_general]
        >> metis_tac [])
  >> qexists_tac `word_after78`
  >> qexists_tac `packets`
  >> qexists_tac `semantic_after78`
  >> qexists_tac `runtime_stack_after78`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
