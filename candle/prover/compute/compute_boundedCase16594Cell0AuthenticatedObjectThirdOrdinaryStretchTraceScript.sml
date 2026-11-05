(*****************************************************************************
 * Genuine authenticated case-16594 trace through instructions 0--119.
 * Instructions 79--119 are the ordinary stretch before the final delta pair.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTrace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectSecondSpecializedPairTrace
  compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariant
  compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_source_stretch79_through119_def:
  bounded_case16594_source_stretch79_through119 =
    TAKE 41 (DROP 79 bounded_case16594_program)
End

Definition bounded_case16594_prepared_stretch79_through119_def:
  bounded_case16594_prepared_stretch79_through119 =
    TAKE 41 (DROP 79 bounded_case16594_prepared_program)
End

Definition bounded_case16594_prepared_suffix_after120_def:
  bounded_case16594_prepared_suffix_after120 =
    DROP 120 bounded_case16594_prepared_program
End

Theorem bounded_case16594_stretch79_through119_general_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_source_stretch79_through119
      bounded_case16594_prepared_stretch79_through119 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_prepared_stretch79_through119 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_source_stretch79_through119 /\
  bounded_case16594_prepared_stretch79_through119 ++
      bounded_case16594_prepared_suffix_after120 =
    bounded_case16594_prepared_suffix_after79
Proof
  conj_tac
  >- (rw
       [bounded_case16594_source_stretch79_through119_def,
        bounded_case16594_prepared_stretch79_through119_def]
      >> irule LIST_REL_TAKE
      >> irule LIST_REL_DROP
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_source_stretch79_through119_def,
        bounded_case16594_prepared_stretch79_through119_def,
        bounded_case16594_prepared_suffix_after120_def,
        compute_boundedCase16594Cell0AuthenticatedObjectSecondSpecializedPairTraceTheory.bounded_case16594_prepared_suffix_after79_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Definition bounded_case16594_source_prefix120_def:
  bounded_case16594_source_prefix120 =
    bounded_case16594_source_prefix79 ++
      bounded_case16594_source_stretch79_through119
End

Definition bounded_case16594_prepared_prefix120_def:
  bounded_case16594_prepared_prefix120 =
    bounded_case16594_prepared_prefix79 ++
      bounded_case16594_prepared_stretch79_through119
End

Definition bounded_case16594_prefix120_codes_cv_def:
  bounded_case16594_prefix120_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix79_codes_cv
      (bounded_case16594_general_codes_cv
        bounded_case16594_source_stretch79_through119)
End

Definition bounded_case16594_prefix120_sources_cv_def:
  bounded_case16594_prefix120_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix79_sources_cv
      (bounded_case16594_analytic_program_cv
        bounded_case16594_source_stretch79_through119)
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through119_trace:
  ?word_after120 packets_after120 semantic_after120 runtime_stack_after120.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after120 word_after120 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after120) /\
    bounded_analytic64_state_covers_object_q word_after120 semantic_after120 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after120) packets_after120 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix120
      bounded_case16594_prepared_prefix120
      bounded_case16594_prefix120_codes_cv
      bounded_case16594_prefix120_sources_cv
      bounded_case16594_authenticated_fast_packets_cv []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after120)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after120))))
      semantic_after120
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectSecondSpecializedPairTraceTheory.bounded_case16594_cell0_authenticated_object_prefix0_through78_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after79
        (FST semantic_after79)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> mp_tac
       (Q.SPECL
         [`bounded_case16594_source_stretch79_through119`,
          `bounded_case16594_prepared_stretch79_through119`,
          `bounded_case16594_prepared_suffix_after120`,
          `word_after79`,
          `bounded_case16594_cell0_authenticated_word_runtime_final_state`,
          `packets_after79`, `runtime_stack_after79`, `semantic_after79`]
         (Q.INST
           [`runtime_radii` |->
              `bounded_case16594_cell0_authenticated_object_radii`,
            `semantic_radii` |-> `bounded_case16594_cell0_source_word_radii`,
            `weights` |-> `bounded_case16594_cell0_authenticated_word_weights`,
            `runtime_center_box_values` |->
              `bounded_case16594_cell0_authenticated_object_center_environment`,
            `runtime_outer_box_values` |->
              `bounded_case16594_cell0_authenticated_object_box_environment`,
            `semantic_center_boxes` |->
              `bounded_case16594_cell0_authenticated_object_center_environment`,
            `semantic_outer_boxes` |->
              `bounded_case16594_cell0_authenticated_object_box_environment`,
            `word_center_boxes` |->
              `bounded_case16594_cell0_source_word_center_environment`,
            `word_outer_boxes` |->
              `bounded_case16594_cell0_authenticated_word_box_environment`]
           compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariantTheory.bounded_case16594_object_joint_general_prefix_trace))
  >> impl_tac
  >- (asm_rewrite_tac
       [bounded_case16594_stretch79_through119_general_contract]
      >> simp
           [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
            compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs,
            compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_payload_lengths,
            compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
            compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_boxes_valid,
            compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_boxes_equivalent,
            compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
            compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated])
  >> disch_then
       (qx_choose_then `word_after120`
         (qx_choose_then `packets_after120`
           (qx_choose_then `semantic_after120`
             (qx_choose_then `runtime_stack_after120` strip_assume_tac))))
  >> fs
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
        bounded_case16594_source_prefix120
        bounded_case16594_prepared_prefix120
        bounded_case16594_prefix120_codes_cv
        bounded_case16594_prefix120_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after120)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after120))))
        semantic_after120` by
       (rw
          [bounded_case16594_source_prefix120_def,
           bounded_case16594_prepared_prefix120_def,
           bounded_case16594_prefix120_codes_cv_def,
           bounded_case16594_prefix120_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after79)`
        >> qexists_tac `runtime_stack_after79`
        >> qexists_tac `semantic_after79`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after120`
  >> qexists_tac `packets_after120`
  >> qexists_tac `semantic_after120`
  >> qexists_tac `runtime_stack_after120`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
