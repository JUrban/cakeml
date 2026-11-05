(*****************************************************************************
 * Genuine authenticated case-16594 trace across the final specialized pair.
 * Positions 120 and 121 are -d(delta)/dx_5 and 4*x_2*delta.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectThirdSpecializedPairTrace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTrace
  compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariant
  compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_prepared_suffix_after121_def:
  bounded_case16594_prepared_suffix_after121 =
    DROP 121 bounded_case16594_prepared_program
End

Theorem bounded_case16594_prepared_suffix_after120_unfold:
  bounded_case16594_prepared_suffix_after120 =
    BoundedAnalytic64NegDeltaDerivative 5 ::
      bounded_case16594_prepared_suffix_after121
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTraceTheory.bounded_case16594_prepared_suffix_after120_def,
     bounded_case16594_prepared_suffix_after121_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source120_decode_and_refines:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source120_cv =
      SOME (EL 120 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 120 bounded_case16594_program)
    (BoundedAnalytic64NegDeltaDerivative 5)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source120_cv_def]
      >> irule
           compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_object_cv_nth_decodes
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source120_specialization_ok]
QED

Definition bounded_case16594_source_prefix121_def:
  bounded_case16594_source_prefix121 =
    bounded_case16594_source_prefix120 ++ [EL 120 bounded_case16594_program]
End

Definition bounded_case16594_prepared_prefix121_def:
  bounded_case16594_prepared_prefix121 =
    bounded_case16594_prepared_prefix120 ++
      [BoundedAnalytic64NegDeltaDerivative 5]
End

Definition bounded_case16594_prefix121_codes_cv_def:
  bounded_case16594_prefix121_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix120_codes_cv (Pair (Num 6) (Num 0))
End

Definition bounded_case16594_prefix121_sources_cv_def:
  bounded_case16594_prefix121_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix120_sources_cv
      (Pair bounded_case16594_object_source120_cv (Num 0))
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through120_trace:
  ?word_after121 packets_after121 semantic_after121 runtime_stack_after121.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after121 word_after121 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after121) /\
    bounded_analytic64_state_covers_object_q word_after121 semantic_after121 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after121) packets_after121 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix121
      bounded_case16594_prepared_prefix121
      bounded_case16594_prefix121_codes_cv
      bounded_case16594_prefix121_sources_cv
      bounded_case16594_authenticated_fast_packets_cv []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after121)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after121))))
      semantic_after121
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTraceTheory.bounded_case16594_cell0_authenticated_object_prefix0_through119_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after120
        (FST semantic_after120)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> qpat_x_assum
       `bounded_analytic64_program_runtime_certificate_trace _ _ _
          bounded_case16594_prepared_suffix_after120 word_after120 = _`
       mp_tac
  >> rw [bounded_case16594_prepared_suffix_after120_unfold]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet120`
         (qx_choose_then `word_after121`
           (qx_choose_then `packets_after121` strip_assume_tac)))
  >> `packet120 = [] /\ SND word_after121 = SND word_after120` by
       metis_tac
         [compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_neg5_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_neg_derivative
          bounded_case16594_cell0_source_word_radii
          bounded_case16594_cell0_source_word_center_environment 5 =
            SOME word_result` by
       (Cases_on `word_after120`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_neg_refinement_context
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment 5` by
       (match_mp_tac
          (Q.INST
            [`coordinate` |-> `5`,
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
          `word_state` |-> `word_after120`,
          `semantic_state` |-> `semantic_after120`,
          `word_center_boxes` |->
            `bounded_case16594_cell0_source_word_center_environment`,
          `word_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_word_box_environment`,
          `word_next` |-> `word_after121`,
          `packet_rest` |-> `packets_after120`,
          `runtime_stack` |-> `runtime_stack_after120`]
         compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_neg5_runtime_step)
  >> impl_tac
  >- simp
       [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated]
  >> disch_then
       (qx_choose_then `semantic_after121`
         (qx_choose_then `runtime_stack_after121` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        (Num 6) bounded_case16594_object_source120_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after120))
        (bounded_object_q_cv_list runtime_stack_after120)
        (bounded_object_q_cv_list runtime_stack_after121)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after120))` by
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
        [EL 120 bounded_case16594_program]
        [BoundedAnalytic64NegDeltaDerivative 5]
        (Pair (Num 6) (Num 0))
        (Pair bounded_case16594_object_source120_cv (Num 0))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after120))
        runtime_stack_after120 semantic_after120
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after121)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after120))))
        semantic_after121` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source120_decode_and_refines]
        >> metis_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_source_prefix121
        bounded_case16594_prepared_prefix121
        bounded_case16594_prefix121_codes_cv
        bounded_case16594_prefix121_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after121)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after120))))
        semantic_after121` by
       (rw
          [bounded_case16594_source_prefix121_def,
           bounded_case16594_prepared_prefix121_def,
           bounded_case16594_prefix121_codes_cv_def,
           bounded_case16594_prefix121_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after120)`
        >> qexists_tac `runtime_stack_after120`
        >> qexists_tac `semantic_after120`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after121`
  >> qexists_tac `packets_after120`
  >> qexists_tac `semantic_after121`
  >> qexists_tac `runtime_stack_after121`
  >> asm_rewrite_tac []
QED

Definition bounded_case16594_prepared_suffix_after122_def:
  bounded_case16594_prepared_suffix_after122 =
    DROP 122 bounded_case16594_prepared_program
End

Theorem bounded_case16594_prepared_suffix_after121_unfold:
  bounded_case16594_prepared_suffix_after121 =
    BoundedAnalytic64FourCoordinateDelta 2 ::
      bounded_case16594_prepared_suffix_after122
Proof
  simp
    [bounded_case16594_prepared_suffix_after121_def,
     bounded_case16594_prepared_suffix_after122_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source121_decode_and_refines:
  bounded_analytic_instruction_of_cv bounded_case16594_object_source121_cv =
      SOME (EL 121 bounded_case16594_program) /\
  bounded_analytic_instruction_refines 6 (EL 121 bounded_case16594_program)
    (BoundedAnalytic64FourCoordinateDelta 2)
Proof
  conj_tac
  >- (rw
        [compute_boundedCase16594ObjectSpecializedStepControlEvalTheory.bounded_case16594_object_source121_cv_def]
      >> irule
           compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_object_cv_nth_decodes
      >> simp
           [compute_boundedCase16594SourceCVDataTheory.bounded_case16594_source_program_cv_decodes]
      >> EVAL_TAC)
  >> simp
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source121_specialization_ok]
QED

Definition bounded_case16594_source_prefix122_def:
  bounded_case16594_source_prefix122 =
    bounded_case16594_source_prefix121 ++ [EL 121 bounded_case16594_program]
End

Definition bounded_case16594_prepared_prefix122_def:
  bounded_case16594_prepared_prefix122 =
    bounded_case16594_prepared_prefix121 ++
      [BoundedAnalytic64FourCoordinateDelta 2]
End

Definition bounded_case16594_prefix122_codes_cv_def:
  bounded_case16594_prefix122_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix121_codes_cv (Pair (Num 3) (Num 0))
End

Definition bounded_case16594_prefix122_sources_cv_def:
  bounded_case16594_prefix122_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix121_sources_cv
      (Pair bounded_case16594_object_source121_cv (Num 0))
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through121_trace:
  ?word_after122 packets_after122 semantic_after122 runtime_stack_after122.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after122 word_after122 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after122) /\
    bounded_analytic64_state_covers_object_q word_after122 semantic_after122 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after122) packets_after122 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix122
      bounded_case16594_prepared_prefix122
      bounded_case16594_prefix122_codes_cv
      bounded_case16594_prefix122_sources_cv
      bounded_case16594_authenticated_fast_packets_cv []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after122)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after122))))
      semantic_after122
Proof
  mp_tac bounded_case16594_cell0_authenticated_object_prefix0_through120_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after121
        (FST semantic_after121)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> qpat_x_assum
       `bounded_analytic64_program_runtime_certificate_trace _ _ _
          bounded_case16594_prepared_suffix_after121 word_after121 = _`
       mp_tac
  >> rw [bounded_case16594_prepared_suffix_after121_unfold]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet121`
         (qx_choose_then `word_after122`
           (qx_choose_then `packets_after122` strip_assume_tac)))
  >> `packet121 = [] /\ SND word_after122 = SND word_after121` by
       metis_tac
         [compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_product2_packet_state]
  >> gvs []
  >> `?word_result.
        bounded_delta64_four_coordinate
          bounded_case16594_cell0_source_word_radii
          bounded_case16594_cell0_source_word_center_environment
          bounded_case16594_cell0_authenticated_word_box_environment 2 =
            SOME word_result` by
       (Cases_on `word_after121`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_case16594_object_delta_product_refinement_context
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment 2` by
       (match_mp_tac
          (Q.INST
            [`coordinate` |-> `2`,
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
          `word_state` |-> `word_after121`,
          `semantic_state` |-> `semantic_after121`,
          `word_center_boxes` |->
            `bounded_case16594_cell0_source_word_center_environment`,
          `word_outer_boxes` |->
            `bounded_case16594_cell0_authenticated_word_box_environment`,
          `word_next` |-> `word_after122`,
          `packet_rest` |-> `packets_after121`,
          `runtime_stack` |-> `runtime_stack_after121`]
         compute_boundedCase16594ObjectThirdSpecializedRuntimeDispatchInvariantTheory.bounded_case16594_object_joint_product2_runtime_step)
  >> impl_tac
  >- simp
       [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated]
  >> disch_then
       (qx_choose_then `semantic_after122`
         (qx_choose_then `runtime_stack_after122` strip_assume_tac))
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        (Num 3) bounded_case16594_object_source121_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after121))
        (bounded_object_q_cv_list runtime_stack_after121)
        (bounded_object_q_cv_list runtime_stack_after122)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after121))` by
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
        [EL 121 bounded_case16594_program]
        [BoundedAnalytic64FourCoordinateDelta 2]
        (Pair (Num 3) (Num 0))
        (Pair bounded_case16594_object_source121_cv (Num 0))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets_after121))
        runtime_stack_after121 semantic_after121
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after122)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after121))))
        semantic_after122` by
       (simp
          [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
           bounded_case16594_object_source121_decode_and_refines]
        >> metis_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_source_prefix122
        bounded_case16594_prepared_prefix122
        bounded_case16594_prefix122_codes_cv
        bounded_case16594_prefix122_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after122)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after121))))
        semantic_after122` by
       (rw
          [bounded_case16594_source_prefix122_def,
           bounded_case16594_prepared_prefix122_def,
           bounded_case16594_prefix122_codes_cv_def,
           bounded_case16594_prefix122_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after121)`
        >> qexists_tac `runtime_stack_after121`
        >> qexists_tac `semantic_after121`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after122`
  >> qexists_tac `packets_after121`
  >> qexists_tac `semantic_after122`
  >> qexists_tac `runtime_stack_after122`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();

