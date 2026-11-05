(*****************************************************************************
 * Genuine authenticated case-16594 trace through instructions 0--33.
 *
 * The first theorem factors the authenticated cell-0 environment out of the
 * generic all-ordinary-prefix induction.  The second theorem instantiates it
 * with TAKE 34, stopping immediately before the first specialized delta pair.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectPrefix34Trace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectPrefix10Trace
Libs
  bossLib preamble wordsLib intLib

Theorem bounded_case16594_cell0_authenticated_object_general_prefix_trace:
  !source_prefix prepared_prefix prepared_suffix.
    LIST_REL (bounded_analytic_instruction_refines 6)
      source_prefix prepared_prefix /\
    EVERY bounded_analytic64_ordinary_instruction prepared_prefix /\
    EVERY bounded_case16594_object_dispatch_source_clock_ok source_prefix /\
    prepared_prefix ++ prepared_suffix = bounded_case16594_prepared_program
    ==>
    ?word_middle packets_remaining semantic_middle runtime_stack_middle.
      bounded_analytic64_program_runtime_certificate_trace
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_source_word_center_environment
        bounded_case16594_cell0_authenticated_word_box_environment
        prepared_suffix word_middle =
          SOME
            (bounded_case16594_cell0_authenticated_word_runtime_final_state,
             packets_remaining) /\
      bounded_analytic64_state_covers_object_q word_middle semantic_middle /\
      bounded_case16594_word_dispatch_packet_contracts
        (SND word_middle) packets_remaining /\
      bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        source_prefix prepared_prefix
        (bounded_case16594_general_codes_cv source_prefix)
        (bounded_case16594_analytic_program_cv source_prefix)
        bounded_case16594_authenticated_fast_packets_cv
        []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_middle)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_remaining))))
        semantic_middle
Proof
  rpt gen_tac
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`source_prefix`, `prepared_prefix`, `prepared_suffix`,
          `([],bounded_case16594_cell0_source_word_certificates)`,
          `bounded_case16594_cell0_authenticated_word_runtime_final_state`,
          `bounded_case16594_cell0_authenticated_word_runtime_packets`,
          `[]`,
          `([],bounded_case16594_cell0_source_word_certificates)`]
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
  >- (asm_rewrite_tac []
      >> simp
           [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_radii_encoded,
            compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs,
            compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_payload_lengths,
            compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
            compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_boxes_valid,
            compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_object_boxes_equivalent,
            compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_cell0_authenticated_word_runtime_trace_named,
            compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
            compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated,
            compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_cell0_word_dispatch_packet_contracts,
            compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
            compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def])
  >> simp
       [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_center_payload_identity,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_box_payload_identity,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_payload_identity,
        compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_fast_packets_cv_def]
QED

Definition bounded_case16594_source_prefix34_def:
  bounded_case16594_source_prefix34 = TAKE 34 bounded_case16594_program
End

Definition bounded_case16594_prepared_prefix34_def:
  bounded_case16594_prepared_prefix34 =
    TAKE 34 bounded_case16594_prepared_program
End

Definition bounded_case16594_prepared_suffix_after34_def:
  bounded_case16594_prepared_suffix_after34 =
    DROP 34 bounded_case16594_prepared_program
End

Definition bounded_case16594_prefix34_codes_cv_def:
  bounded_case16594_prefix34_codes_cv =
    bounded_case16594_general_codes_cv bounded_case16594_source_prefix34
End

Definition bounded_case16594_prefix34_sources_cv_def:
  bounded_case16594_prefix34_sources_cv =
    bounded_case16594_analytic_program_cv bounded_case16594_source_prefix34
End

Theorem bounded_case16594_prefix34_general_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_source_prefix34
      bounded_case16594_prepared_prefix34 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_prepared_prefix34 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_source_prefix34 /\
  bounded_case16594_prepared_prefix34 ++
      bounded_case16594_prepared_suffix_after34 =
    bounded_case16594_prepared_program
Proof
  conj_tac
  >- (rw
       [bounded_case16594_source_prefix34_def,
        bounded_case16594_prepared_prefix34_def]
      >> irule LIST_REL_TAKE
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_source_prefix34_def,
        bounded_case16594_prepared_prefix34_def,
        bounded_case16594_prepared_suffix_after34_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through33_trace:
  ?word_after34 packets_after34 semantic_after34 runtime_stack_after34.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after34 word_after34 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after34) /\
    bounded_analytic64_state_covers_object_q word_after34 semantic_after34 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after34) packets_after34 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix34
      bounded_case16594_prepared_prefix34
      bounded_case16594_prefix34_codes_cv
      bounded_case16594_prefix34_sources_cv
      bounded_case16594_authenticated_fast_packets_cv
      []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after34)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after34))))
      semantic_after34
Proof
  mp_tac
    (Q.SPECL
      [`bounded_case16594_source_prefix34`,
       `bounded_case16594_prepared_prefix34`,
       `bounded_case16594_prepared_suffix_after34`]
      bounded_case16594_cell0_authenticated_object_general_prefix_trace)
  >> impl_tac
  >- ACCEPT_TAC bounded_case16594_prefix34_general_contract
  >> simp
       [bounded_case16594_prefix34_codes_cv_def,
        bounded_case16594_prefix34_sources_cv_def]
QED

val _ = export_theory ();
