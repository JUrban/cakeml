(*****************************************************************************
 * Genuine authenticated case-16594 trace across the first specialized pair.
 *
 * Positions 34 and 35 are respectively -d(delta)/dx_3 and 4*x_0*delta.
 * This theory instantiates the generic joint specialized-step adapters at
 * the authenticated cell-0 environment and appends them to the established
 * trace through positions 0--33.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTrace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectPrefix34Trace
  compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariant
  compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_prepared_suffix_after35_def:
  bounded_case16594_prepared_suffix_after35 =
    DROP 35 bounded_case16594_prepared_program
End

Theorem bounded_case16594_prepared_suffix_after34_unfold:
  bounded_case16594_prepared_suffix_after34 =
    BoundedAnalytic64NegDeltaDerivative 3 ::
      bounded_case16594_prepared_suffix_after35
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedObjectPrefix34TraceTheory.bounded_case16594_prepared_suffix_after34_def,
     bounded_case16594_prepared_suffix_after35_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_cv_nth_decodes:
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

Theorem bounded_case16594_object_source34_decode_and_refines:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source34_cv =
      SOME (EL 34 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 34 bounded_case16594_program)
    (BoundedAnalytic64NegDeltaDerivative 3)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source34_cv_def]
      >> irule bounded_case16594_object_cv_nth_decodes
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source34_specialization_ok]
QED

Theorem bounded_case16594_named_semantic_trace_final_stack:
  bounded_case16594_object_dispatch_semantic_trace step_floor
    runtime_center_boxes runtime_outer_boxes runtime_radii
    semantic_radii weights semantic_center_boxes semantic_outer_boxes
    source_program prepared_program runtime_codes runtime_sources
    runtime_certificates initial_runtime_stack initial_semantic_state
    (Pair (Num 1)
      (Pair (bounded_object_q_cv_list final_runtime_stack)
        final_runtime_certificates))
    final_semantic_state
  ==>
  bounded_object_q_taylor_stack_runtime_refines final_runtime_stack
    (FST final_semantic_state)
Proof
  strip_tac
  >> drule
       compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_final_stack
  >> disch_then
       (qx_choose_then `witness_stack`
         (qx_choose_then `witness_certificates` strip_assume_tac))
  >> `witness_stack = final_runtime_stack` by
       (irule
          compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_q_cv_list_injective
        >> fs [])
  >> gvs []
QED

Definition bounded_case16594_source_prefix35_def:
  bounded_case16594_source_prefix35 =
    bounded_case16594_source_prefix34 ++ [EL 34 bounded_case16594_program]
End

Definition bounded_case16594_prepared_prefix35_def:
  bounded_case16594_prepared_prefix35 =
    bounded_case16594_prepared_prefix34 ++
      [BoundedAnalytic64NegDeltaDerivative 3]
End

Definition bounded_case16594_prefix35_codes_cv_def:
  bounded_case16594_prefix35_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix34_codes_cv (Pair (Num 4) (Num 0))
End

Definition bounded_case16594_prefix35_sources_cv_def:
  bounded_case16594_prefix35_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix34_sources_cv
      (Pair bounded_case16594_object_source34_cv (Num 0))
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through34_trace:
  ?word_after35 packets_after35 semantic_after35 runtime_stack_after35.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after35 word_after35 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after35) /\
    bounded_analytic64_state_covers_object_q word_after35 semantic_after35 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after35) packets_after35 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix35
      bounded_case16594_prepared_prefix35
      bounded_case16594_prefix35_codes_cv
      bounded_case16594_prefix35_sources_cv
      bounded_case16594_authenticated_fast_packets_cv
      []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after35)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after35))))
      semantic_after35
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectPrefix34TraceTheory.bounded_case16594_cell0_authenticated_object_prefix0_through33_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after34
        (FST semantic_after34)` by
       metis_tac [bounded_case16594_named_semantic_trace_final_stack]
  >> qpat_x_assum
       `bounded_analytic64_program_runtime_certificate_trace _ _ _
          bounded_case16594_prepared_suffix_after34 word_after34 = _`
       mp_tac
  >> rw [bounded_case16594_prepared_suffix_after34_unfold]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet34`
         (qx_choose_then `word_after35`
           (qx_choose_then `packets_after35` strip_assume_tac)))
  >> `packet34 = [] /\ SND word_after35 = SND word_after34` by
       metis_tac
         [compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_neg3_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_neg_derivative
          bounded_case16594_cell0_source_word_radii
          bounded_case16594_cell0_source_word_center_environment 3 =
            SOME word_result` by
       (Cases_on `word_after34`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_neg_refinement_context
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment 3` by
       (match_mp_tac
          (Q.INST
            [`coordinate` |-> `3`,
             `object_center_environment` |->
               `bounded_case16594_cell0_authenticated_object_center_environment`,
             `word_center_environment` |->
               `bounded_case16594_cell0_source_word_center_environment`,
             `semantic_radii` |->
               `bounded_case16594_cell0_source_word_radii`,
             `weights` |->
               `bounded_case16594_cell0_authenticated_word_weights`,
             `word_result` |-> `word_result`]
            compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_delta_neg_refinement_context_from_word)
        >> simp
             [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_payload_lengths,
              compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
              compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs])
  >> mp_tac
       (Q.INST
         [`semantic_radii` |->
            `bounded_case16594_cell0_source_word_radii`,
          `weights` |->
            `bounded_case16594_cell0_authenticated_word_weights`,
          `semantic_center_boxes` |->
            `bounded_case16594_cell0_authenticated_object_center_environment`,
          `semantic_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_object_box_environment`,
          `runtime_radii` |->
            `bounded_case16594_cell0_authenticated_object_radii`,
          `word_state` |-> `word_after34`,
          `semantic_state` |-> `semantic_after34`,
          `word_center_boxes` |->
            `bounded_case16594_cell0_source_word_center_environment`,
          `word_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_word_box_environment`,
          `word_next` |-> `word_after35`,
          `packet_rest` |-> `packets_after34`,
          `runtime_stack` |-> `runtime_stack_after34`]
         compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_neg3_runtime_step)
  >> impl_tac
  >- simp
       [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated]
  >> disch_then
       (qx_choose_then `semantic_after35`
         (qx_choose_then `runtime_stack_after35` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        (Num 4) bounded_case16594_object_source34_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after34))
        (bounded_object_q_cv_list runtime_stack_after34)
        (bounded_object_q_cv_list runtime_stack_after35)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after34))` by
       fs
         [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_center_payload_identity,
          compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_box_payload_identity,
          compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_payload_identity]
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        [EL 34 bounded_case16594_program]
        [BoundedAnalytic64NegDeltaDerivative 3]
        (Pair (Num 4) (Num 0))
        (Pair bounded_case16594_object_source34_cv (Num 0))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after34))
        runtime_stack_after34 semantic_after34
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after35)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after34))))
        semantic_after35` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source34_decode_and_refines]
        >> metis_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_source_prefix35
        bounded_case16594_prepared_prefix35
        bounded_case16594_prefix35_codes_cv
        bounded_case16594_prefix35_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after35)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after34))))
        semantic_after35` by
       (rw
          [bounded_case16594_source_prefix35_def,
           bounded_case16594_prepared_prefix35_def,
           bounded_case16594_prefix35_codes_cv_def,
           bounded_case16594_prefix35_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after34)`
        >> qexists_tac `runtime_stack_after34`
        >> qexists_tac `semantic_after34`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after35`
  >> qexists_tac `packets_after34`
  >> qexists_tac `semantic_after35`
  >> qexists_tac `runtime_stack_after35`
  >> asm_rewrite_tac []
QED

Definition bounded_case16594_prepared_suffix_after36_def:
  bounded_case16594_prepared_suffix_after36 =
    DROP 36 bounded_case16594_prepared_program
End

Theorem bounded_case16594_prepared_suffix_after35_unfold:
  bounded_case16594_prepared_suffix_after35 =
    BoundedAnalytic64FourCoordinateDelta 0 ::
      bounded_case16594_prepared_suffix_after36
Proof
  simp
    [bounded_case16594_prepared_suffix_after35_def,
     bounded_case16594_prepared_suffix_after36_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source35_decode_and_refines:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source35_cv =
      SOME (EL 35 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 35 bounded_case16594_program)
    (BoundedAnalytic64FourCoordinateDelta 0)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source35_cv_def]
      >> irule bounded_case16594_object_cv_nth_decodes
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source35_specialization_ok]
QED

Definition bounded_case16594_source_prefix36_def:
  bounded_case16594_source_prefix36 =
    bounded_case16594_source_prefix35 ++ [EL 35 bounded_case16594_program]
End

Definition bounded_case16594_prepared_prefix36_def:
  bounded_case16594_prepared_prefix36 =
    bounded_case16594_prepared_prefix35 ++
      [BoundedAnalytic64FourCoordinateDelta 0]
End

Definition bounded_case16594_prefix36_codes_cv_def:
  bounded_case16594_prefix36_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix35_codes_cv (Pair (Num 1) (Num 0))
End

Definition bounded_case16594_prefix36_sources_cv_def:
  bounded_case16594_prefix36_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix35_sources_cv
      (Pair bounded_case16594_object_source35_cv (Num 0))
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through35_trace:
  ?word_after36 packets_after36 semantic_after36 runtime_stack_after36.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after36 word_after36 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after36) /\
    bounded_analytic64_state_covers_object_q word_after36 semantic_after36 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after36) packets_after36 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix36
      bounded_case16594_prepared_prefix36
      bounded_case16594_prefix36_codes_cv
      bounded_case16594_prefix36_sources_cv
      bounded_case16594_authenticated_fast_packets_cv
      []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after36)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after36))))
      semantic_after36
Proof
  mp_tac bounded_case16594_cell0_authenticated_object_prefix0_through34_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after35
        (FST semantic_after35)` by
       metis_tac [bounded_case16594_named_semantic_trace_final_stack]
  >> qpat_x_assum
       `bounded_analytic64_program_runtime_certificate_trace _ _ _
          bounded_case16594_prepared_suffix_after35 word_after35 = _`
       mp_tac
  >> rw [bounded_case16594_prepared_suffix_after35_unfold]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet35`
         (qx_choose_then `word_after36`
           (qx_choose_then `packets_after36` strip_assume_tac)))
  >> `packet35 = [] /\ SND word_after36 = SND word_after35` by
       metis_tac
         [compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_product0_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_four_coordinate
          bounded_case16594_cell0_source_word_radii
          bounded_case16594_cell0_source_word_center_environment
          bounded_case16594_cell0_authenticated_word_box_environment 0 =
            SOME word_result` by
       (Cases_on `word_after35`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_product_refinement_context
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment 0` by
       (match_mp_tac
          (Q.INST
            [`coordinate` |-> `0`,
             `object_center_environment` |->
               `bounded_case16594_cell0_authenticated_object_center_environment`,
             `object_outer_environment` |->
               `bounded_case16594_cell0_authenticated_object_box_environment`,
             `word_center_environment` |->
               `bounded_case16594_cell0_source_word_center_environment`,
             `word_outer_environment` |->
               `bounded_case16594_cell0_authenticated_word_box_environment`,
             `semantic_radii` |->
               `bounded_case16594_cell0_source_word_radii`,
             `weights` |->
               `bounded_case16594_cell0_authenticated_word_weights`,
             `word_result` |-> `word_result`]
            compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_delta_product_refinement_context_from_word)
        >> simp
             [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_payload_lengths,
              compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
              compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated,
              compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs])
  >> mp_tac
       (Q.INST
         [`semantic_radii` |->
            `bounded_case16594_cell0_source_word_radii`,
          `weights` |->
            `bounded_case16594_cell0_authenticated_word_weights`,
          `semantic_center_boxes` |->
            `bounded_case16594_cell0_authenticated_object_center_environment`,
          `semantic_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_object_box_environment`,
          `runtime_radii` |->
            `bounded_case16594_cell0_authenticated_object_radii`,
          `word_state` |-> `word_after35`,
          `semantic_state` |-> `semantic_after35`,
          `word_center_boxes` |->
            `bounded_case16594_cell0_source_word_center_environment`,
          `word_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_word_box_environment`,
          `word_next` |-> `word_after36`,
          `packet_rest` |-> `packets_after35`,
          `runtime_stack` |-> `runtime_stack_after35`]
         compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_product0_runtime_step)
  >> impl_tac
  >- simp
       [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated]
  >> disch_then
       (qx_choose_then `semantic_after36`
         (qx_choose_then `runtime_stack_after36` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        (Num 1) bounded_case16594_object_source35_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after35))
        (bounded_object_q_cv_list runtime_stack_after35)
        (bounded_object_q_cv_list runtime_stack_after36)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after35))` by
       fs
         [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_center_payload_identity,
          compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_box_payload_identity,
          compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_payload_identity]
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        [EL 35 bounded_case16594_program]
        [BoundedAnalytic64FourCoordinateDelta 0]
        (Pair (Num 1) (Num 0))
        (Pair bounded_case16594_object_source35_cv (Num 0))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after35))
        runtime_stack_after35 semantic_after35
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after36)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after35))))
        semantic_after36` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source35_decode_and_refines]
        >> metis_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_source_prefix36
        bounded_case16594_prepared_prefix36
        bounded_case16594_prefix36_codes_cv
        bounded_case16594_prefix36_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after36)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after35))))
        semantic_after36` by
       (rw
          [bounded_case16594_source_prefix36_def,
           bounded_case16594_prepared_prefix36_def,
           bounded_case16594_prefix36_codes_cv_def,
           bounded_case16594_prefix36_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after35)`
        >> qexists_tac `runtime_stack_after35`
        >> qexists_tac `semantic_after35`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after36`
  >> qexists_tac `packets_after35`
  >> qexists_tac `semantic_after36`
  >> qexists_tac `runtime_stack_after36`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
