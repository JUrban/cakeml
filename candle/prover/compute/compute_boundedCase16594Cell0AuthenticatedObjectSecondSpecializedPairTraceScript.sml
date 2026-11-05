(*****************************************************************************
 * Genuine authenticated case-16594 trace across the second specialized pair.
 * Positions 77 and 78 are -d(delta)/dx_4 and 4*x_1*delta.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectSecondSpecializedPairTrace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectSecondOrdinaryStretchTrace
  compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariant
  compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_prepared_suffix_after78_def:
  bounded_case16594_prepared_suffix_after78 =
    DROP 78 bounded_case16594_prepared_program
End

Theorem bounded_case16594_prepared_suffix_after77_unfold:
  bounded_case16594_prepared_suffix_after77 =
    BoundedAnalytic64NegDeltaDerivative 4 ::
      bounded_case16594_prepared_suffix_after78
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedObjectSecondOrdinaryStretchTraceTheory.bounded_case16594_prepared_suffix_after77_def,
     bounded_case16594_prepared_suffix_after78_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source77_decode_and_refines:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source77_cv =
      SOME (EL 77 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 77 bounded_case16594_program)
    (BoundedAnalytic64NegDeltaDerivative 4)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source77_cv_def]
      >> irule
           compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_object_cv_nth_decodes
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source77_specialization_ok]
QED

Definition bounded_case16594_source_prefix78_def:
  bounded_case16594_source_prefix78 =
    bounded_case16594_source_prefix77 ++ [EL 77 bounded_case16594_program]
End

Definition bounded_case16594_prepared_prefix78_def:
  bounded_case16594_prepared_prefix78 =
    bounded_case16594_prepared_prefix77 ++
      [BoundedAnalytic64NegDeltaDerivative 4]
End

Definition bounded_case16594_prefix78_codes_cv_def:
  bounded_case16594_prefix78_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix77_codes_cv (Pair (Num 5) (Num 0))
End

Definition bounded_case16594_prefix78_sources_cv_def:
  bounded_case16594_prefix78_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix77_sources_cv
      (Pair bounded_case16594_object_source77_cv (Num 0))
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through77_trace:
  ?word_after78 packets_after78 semantic_after78 runtime_stack_after78.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after78 word_after78 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after78) /\
    bounded_analytic64_state_covers_object_q word_after78 semantic_after78 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after78) packets_after78 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix78
      bounded_case16594_prepared_prefix78
      bounded_case16594_prefix78_codes_cv
      bounded_case16594_prefix78_sources_cv
      bounded_case16594_authenticated_fast_packets_cv []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after78)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after78))))
      semantic_after78
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectSecondOrdinaryStretchTraceTheory.bounded_case16594_cell0_authenticated_object_prefix0_through76_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after77
        (FST semantic_after77)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> qpat_x_assum
       `bounded_analytic64_program_runtime_certificate_trace _ _ _
          bounded_case16594_prepared_suffix_after77 word_after77 = _`
       mp_tac
  >> rw [bounded_case16594_prepared_suffix_after77_unfold]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet77`
         (qx_choose_then `word_after78`
           (qx_choose_then `packets_after78` strip_assume_tac)))
  >> `packet77 = [] /\ SND word_after78 = SND word_after77` by
       metis_tac
         [compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_neg4_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_neg_derivative
          bounded_case16594_cell0_source_word_radii
          bounded_case16594_cell0_source_word_center_environment 4 =
            SOME word_result` by
       (Cases_on `word_after77`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_neg_refinement_context
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment 4` by
       (match_mp_tac
          (Q.INST
            [`coordinate` |-> `4`,
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
          `word_state` |-> `word_after77`,
          `semantic_state` |-> `semantic_after77`,
          `word_center_boxes` |->
            `bounded_case16594_cell0_source_word_center_environment`,
          `word_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_word_box_environment`,
          `word_next` |-> `word_after78`,
          `packet_rest` |-> `packets_after77`,
          `runtime_stack` |-> `runtime_stack_after77`]
         compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_neg4_runtime_step)
  >> impl_tac
  >- simp
       [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated]
  >> disch_then
       (qx_choose_then `semantic_after78`
         (qx_choose_then `runtime_stack_after78` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        (Num 5) bounded_case16594_object_source77_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after77))
        (bounded_object_q_cv_list runtime_stack_after77)
        (bounded_object_q_cv_list runtime_stack_after78)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after77))` by
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
        [EL 77 bounded_case16594_program]
        [BoundedAnalytic64NegDeltaDerivative 4]
        (Pair (Num 5) (Num 0))
        (Pair bounded_case16594_object_source77_cv (Num 0))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after77))
        runtime_stack_after77 semantic_after77
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after78)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after77))))
        semantic_after78` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source77_decode_and_refines]
        >> metis_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_source_prefix78
        bounded_case16594_prepared_prefix78
        bounded_case16594_prefix78_codes_cv
        bounded_case16594_prefix78_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after78)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after77))))
        semantic_after78` by
       (rw
          [bounded_case16594_source_prefix78_def,
           bounded_case16594_prepared_prefix78_def,
           bounded_case16594_prefix78_codes_cv_def,
           bounded_case16594_prefix78_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after77)`
        >> qexists_tac `runtime_stack_after77`
        >> qexists_tac `semantic_after77`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after78`
  >> qexists_tac `packets_after77`
  >> qexists_tac `semantic_after78`
  >> qexists_tac `runtime_stack_after78`
  >> asm_rewrite_tac []
QED

Definition bounded_case16594_prepared_suffix_after79_def:
  bounded_case16594_prepared_suffix_after79 =
    DROP 79 bounded_case16594_prepared_program
End

Theorem bounded_case16594_prepared_suffix_after78_unfold:
  bounded_case16594_prepared_suffix_after78 =
    BoundedAnalytic64FourCoordinateDelta 1 ::
      bounded_case16594_prepared_suffix_after79
Proof
  simp
    [bounded_case16594_prepared_suffix_after78_def,
     bounded_case16594_prepared_suffix_after79_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source78_decode_and_refines:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source78_cv =
      SOME (EL 78 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 78 bounded_case16594_program)
    (BoundedAnalytic64FourCoordinateDelta 1)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source78_cv_def]
      >> irule
           compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_object_cv_nth_decodes
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source78_specialization_ok]
QED

Definition bounded_case16594_source_prefix79_def:
  bounded_case16594_source_prefix79 =
    bounded_case16594_source_prefix78 ++ [EL 78 bounded_case16594_program]
End

Definition bounded_case16594_prepared_prefix79_def:
  bounded_case16594_prepared_prefix79 =
    bounded_case16594_prepared_prefix78 ++
      [BoundedAnalytic64FourCoordinateDelta 1]
End

Definition bounded_case16594_prefix79_codes_cv_def:
  bounded_case16594_prefix79_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix78_codes_cv (Pair (Num 2) (Num 0))
End

Definition bounded_case16594_prefix79_sources_cv_def:
  bounded_case16594_prefix79_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix78_sources_cv
      (Pair bounded_case16594_object_source78_cv (Num 0))
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through78_trace:
  ?word_after79 packets_after79 semantic_after79 runtime_stack_after79.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after79 word_after79 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after79) /\
    bounded_analytic64_state_covers_object_q word_after79 semantic_after79 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after79) packets_after79 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix79
      bounded_case16594_prepared_prefix79
      bounded_case16594_prefix79_codes_cv
      bounded_case16594_prefix79_sources_cv
      bounded_case16594_authenticated_fast_packets_cv []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after79)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after79))))
      semantic_after79
Proof
  mp_tac bounded_case16594_cell0_authenticated_object_prefix0_through77_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after78
        (FST semantic_after78)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> qpat_x_assum
       `bounded_analytic64_program_runtime_certificate_trace _ _ _
          bounded_case16594_prepared_suffix_after78 word_after78 = _`
       mp_tac
  >> rw [bounded_case16594_prepared_suffix_after78_unfold]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet78`
         (qx_choose_then `word_after79`
           (qx_choose_then `packets_after79` strip_assume_tac)))
  >> `packet78 = [] /\ SND word_after79 = SND word_after78` by
       metis_tac
         [compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_product1_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_four_coordinate
          bounded_case16594_cell0_source_word_radii
          bounded_case16594_cell0_source_word_center_environment
          bounded_case16594_cell0_authenticated_word_box_environment 1 =
            SOME word_result` by
       (Cases_on `word_after78`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_product_refinement_context
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment 1` by
       (match_mp_tac
          (Q.INST
            [`coordinate` |-> `1`,
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
          `word_state` |-> `word_after78`,
          `semantic_state` |-> `semantic_after78`,
          `word_center_boxes` |->
            `bounded_case16594_cell0_source_word_center_environment`,
          `word_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_word_box_environment`,
          `word_next` |-> `word_after79`,
          `packet_rest` |-> `packets_after78`,
          `runtime_stack` |-> `runtime_stack_after78`]
         compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_product1_runtime_step)
  >> impl_tac
  >- simp
       [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated]
  >> disch_then
       (qx_choose_then `semantic_after79`
         (qx_choose_then `runtime_stack_after79` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        (Num 2) bounded_case16594_object_source78_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after78))
        (bounded_object_q_cv_list runtime_stack_after78)
        (bounded_object_q_cv_list runtime_stack_after79)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after78))` by
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
        [EL 78 bounded_case16594_program]
        [BoundedAnalytic64FourCoordinateDelta 1]
        (Pair (Num 2) (Num 0))
        (Pair bounded_case16594_object_source78_cv (Num 0))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after78))
        runtime_stack_after78 semantic_after78
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after79)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after78))))
        semantic_after79` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source78_decode_and_refines]
        >> metis_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_source_prefix79
        bounded_case16594_prepared_prefix79
        bounded_case16594_prefix79_codes_cv
        bounded_case16594_prefix79_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after79)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after78))))
        semantic_after79` by
       (rw
          [bounded_case16594_source_prefix79_def,
           bounded_case16594_prepared_prefix79_def,
           bounded_case16594_prefix79_codes_cv_def,
           bounded_case16594_prefix79_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after78)`
        >> qexists_tac `runtime_stack_after78`
        >> qexists_tac `semantic_after78`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after79`
  >> qexists_tac `packets_after78`
  >> qexists_tac `semantic_after79`
  >> qexists_tac `runtime_stack_after79`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
