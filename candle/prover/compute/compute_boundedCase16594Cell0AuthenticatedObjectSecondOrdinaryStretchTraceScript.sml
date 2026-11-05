(*****************************************************************************
 * Genuine authenticated case-16594 trace through instructions 0--76.
 *
 * Instructions 36--76 form the all-ordinary stretch between the first and
 * second specialized delta pairs.  Reuse the generic ordinary-prefix
 * induction from the authenticated state after instruction 35, then compose
 * that segment with the already established prefix trace.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectSecondOrdinaryStretchTrace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTrace
  compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariant
  compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_source_stretch36_through76_def:
  bounded_case16594_source_stretch36_through76 =
    TAKE 41 (DROP 36 bounded_case16594_program)
End

Definition bounded_case16594_prepared_stretch36_through76_def:
  bounded_case16594_prepared_stretch36_through76 =
    TAKE 41 (DROP 36 bounded_case16594_prepared_program)
End

Definition bounded_case16594_prepared_suffix_after77_def:
  bounded_case16594_prepared_suffix_after77 =
    DROP 77 bounded_case16594_prepared_program
End

Theorem bounded_case16594_stretch36_through76_general_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_source_stretch36_through76
      bounded_case16594_prepared_stretch36_through76 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_prepared_stretch36_through76 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_source_stretch36_through76 /\
  bounded_case16594_prepared_stretch36_through76 ++
      bounded_case16594_prepared_suffix_after77 =
    bounded_case16594_prepared_suffix_after36
Proof
  conj_tac
  >- (rw
       [bounded_case16594_source_stretch36_through76_def,
        bounded_case16594_prepared_stretch36_through76_def]
      >> irule LIST_REL_TAKE
      >> irule LIST_REL_DROP
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_source_stretch36_through76_def,
        bounded_case16594_prepared_stretch36_through76_def,
        bounded_case16594_prepared_suffix_after77_def,
        compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_prepared_suffix_after36_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Definition bounded_case16594_source_prefix77_def:
  bounded_case16594_source_prefix77 =
    bounded_case16594_source_prefix36 ++
      bounded_case16594_source_stretch36_through76
End

Definition bounded_case16594_prepared_prefix77_def:
  bounded_case16594_prepared_prefix77 =
    bounded_case16594_prepared_prefix36 ++
      bounded_case16594_prepared_stretch36_through76
End

Definition bounded_case16594_prefix77_codes_cv_def:
  bounded_case16594_prefix77_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix36_codes_cv
      (bounded_case16594_general_codes_cv
        bounded_case16594_source_stretch36_through76)
End

Definition bounded_case16594_prefix77_sources_cv_def:
  bounded_case16594_prefix77_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_prefix36_sources_cv
      (bounded_case16594_analytic_program_cv
        bounded_case16594_source_stretch36_through76)
End

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through76_trace:
  ?word_after77 packets_after77 semantic_after77 runtime_stack_after77.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after77 word_after77 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after77) /\
    bounded_analytic64_state_covers_object_q word_after77 semantic_after77 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after77) packets_after77 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix77
      bounded_case16594_prepared_prefix77
      bounded_case16594_prefix77_codes_cv
      bounded_case16594_prefix77_sources_cv
      bounded_case16594_authenticated_fast_packets_cv
      []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after77)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after77))))
      semantic_after77
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_cell0_authenticated_object_prefix0_through35_trace
  >> strip_tac
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after36
        (FST semantic_after36)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> mp_tac
       (Q.SPECL
         [`bounded_case16594_source_stretch36_through76`,
          `bounded_case16594_prepared_stretch36_through76`,
          `bounded_case16594_prepared_suffix_after77`,
          `word_after36`,
          `bounded_case16594_cell0_authenticated_word_runtime_final_state`,
          `packets_after36`, `runtime_stack_after36`, `semantic_after36`]
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
       [bounded_case16594_stretch36_through76_general_contract]
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
       (qx_choose_then `word_after77`
         (qx_choose_then `packets_after77`
           (qx_choose_then `semantic_after77`
             (qx_choose_then `runtime_stack_after77` strip_assume_tac))))
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
        bounded_case16594_source_prefix77
        bounded_case16594_prepared_prefix77
        bounded_case16594_prefix77_codes_cv
        bounded_case16594_prefix77_sources_cv
        bounded_case16594_authenticated_fast_packets_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after77)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after77))))
        semantic_after77` by
       (rw
          [bounded_case16594_source_prefix77_def,
           bounded_case16594_prepared_prefix77_def,
           bounded_case16594_prefix77_codes_cv_def,
           bounded_case16594_prefix77_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after36)`
        >> qexists_tac `runtime_stack_after36`
        >> qexists_tac `semantic_after36`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after77`
  >> qexists_tac `packets_after77`
  >> qexists_tac `semantic_after77`
  >> qexists_tac `runtime_stack_after77`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
