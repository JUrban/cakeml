(*****************************************************************************
 * Arbitrary-state joint trace for the first specialized case-16594 pair.
 *
 * Positions 34 and 35 are respectively -d(delta)/dx_3 and 4*x_0*delta.
 * Unlike the earlier genuine-cell trace, this theorem quantifies over the
 * boxes, radii, certificate state, word state, semantic state, and runtime
 * stack.  It is the first reusable splice needed by the arbitrary accepted-
 * cell trace: a successful fixed-word suffix supplies the two word steps,
 * while the generic specialized adapters supply the exact semantic and
 * production-evaluator steps.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointFirstSpecializedPairInvariant
Ancestors
  compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariant
  compute_boundedCase16594SourceCVData
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_cv_nth_decodes_general:
  !index encoded program.
    bounded_analytic_program_of_cv encoded = SOME program /\
    index < LENGTH program
    ==>
    bounded_analytic_instruction_of_cv
      (bounded_case16594_object_cv_nth index encoded) =
        SOME (EL index program)
Proof
  Induct_on `program`
  >- simp []
  >> rpt gen_tac
  >> Cases_on `encoded`
  >- (Cases_on `n`
      >> simp
           [compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def])
  >> Cases_on `index`
  >> simp
       [compute_boundedAnalyticProgramCVTheory.bounded_analytic_program_of_cv_def,
        compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_cv_nth_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case16594_object_source34_decode_and_refines_general:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source34_cv =
      SOME (EL 34 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 34 bounded_case16594_program)
    (BoundedAnalytic64NegDeltaDerivative 3)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source34_cv_def]
      >> irule bounded_case16594_object_cv_nth_decodes_general
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source34_specialization_ok]
QED

Theorem bounded_case16594_object_source35_decode_and_refines_general:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source35_cv =
      SOME (EL 35 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 35 bounded_case16594_program)
    (BoundedAnalytic64FourCoordinateDelta 0)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source35_cv_def]
      >> irule bounded_case16594_object_cv_nth_decodes_general
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source35_specialization_ok]
QED

Theorem bounded_case16594_object_joint_first_specialized_pair_trace:
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
    (BoundedAnalytic64NegDeltaDerivative 3 ::
     BoundedAnalytic64FourCoordinateDelta 0 :: prepared_suffix)
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
      [EL 34 bounded_case16594_program;EL 35 bounded_case16594_program]
      [BoundedAnalytic64NegDeltaDerivative 3;
       BoundedAnalytic64FourCoordinateDelta 0]
      (Pair (Num 4) (Pair (Num 1) (Num 0)))
      (Pair bounded_case16594_object_source34_cv
        (Pair bounded_case16594_object_source35_cv (Num 0)))
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
       (qx_choose_then `packet34`
         (qx_choose_then `word_after34`
           (qx_choose_then `packets_after34` strip_assume_tac)))
  >> `packet34 = [] /\ SND word_after34 = SND word_state` by
       metis_tac
         [compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_neg3_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_neg_derivative semantic_radii word_center_boxes 3 =
          SOME word_result` by
       (Cases_on `word_state`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_neg_refinement_context
        semantic_radii weights semantic_center_boxes 3` by
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
          `word_next` |-> `word_after34`,
          `packet_rest` |-> `packets`,
          `runtime_stack` |-> `runtime_stack`]
         compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_neg3_runtime_step)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `semantic_after34`
         (qx_choose_then `runtime_stack_after34` strip_assume_tac))
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet35`
         (qx_choose_then `word_after35`
           (qx_choose_then `packets_after35` strip_assume_tac)))
  >> `packet35 = [] /\ SND word_after35 = SND word_after34` by
       metis_tac
         [compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_product0_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_four_coordinate semantic_radii word_center_boxes
          word_outer_boxes 0 = SOME word_result` by
       (Cases_on `word_after34`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_product_refinement_context
        semantic_radii weights semantic_center_boxes semantic_outer_boxes 0` by
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
          `word_state` |-> `word_after34`,
          `semantic_state` |-> `semantic_after34`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `word_next` |-> `word_after35`,
          `packet_rest` |-> `packets`,
          `runtime_stack` |-> `runtime_stack_after34`]
         compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_product0_runtime_step)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `semantic_after35`
         (qx_choose_then `runtime_stack_after35` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        [EL 34 bounded_case16594_program;EL 35 bounded_case16594_program]
        [BoundedAnalytic64NegDeltaDerivative 3;
         BoundedAnalytic64FourCoordinateDelta 0]
        (Pair (Num 4) (Pair (Num 1) (Num 0)))
        (Pair bounded_case16594_object_source34_cv
          (Pair bounded_case16594_object_source35_cv (Num 0)))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after35)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets))))
        semantic_after35` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source34_decode_and_refines_general,
           bounded_case16594_object_source35_decode_and_refines_general]
        >> metis_tac [])
  >> qexists_tac `word_after35`
  >> qexists_tac `packets`
  >> qexists_tac `semantic_after35`
  >> qexists_tac `runtime_stack_after35`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
