(*****************************************************************************
 * Genuine authenticated case-16594 trace through instructions 0--9.
 *
 * This is the first concrete instance of the joint general-prefix induction.
 * All source instructions, prepared instructions, numerical steps, and flat
 * certificate fields are projected from the already authenticated cell-0
 * data.  The result retains the exact post-prefix word/object/runtime states
 * and the unconsumed certificate suffix for the next instruction.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectPrefix10Trace
Ancestors
  compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariant
  compute_boundedCase16594Cell0AuthenticatedWordObjectBridge
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594ObjectRuntimePreservation
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_source_prefix10_def:
  bounded_case16594_source_prefix10 = TAKE 10 bounded_case16594_program
End

Definition bounded_case16594_prepared_prefix10_def:
  bounded_case16594_prepared_prefix10 =
    TAKE 10 bounded_case16594_prepared_program
End

Definition bounded_case16594_prepared_suffix_after10_def:
  bounded_case16594_prepared_suffix_after10 =
    DROP 10 bounded_case16594_prepared_program
End

Definition bounded_case16594_prefix10_codes_cv_def:
  bounded_case16594_prefix10_codes_cv =
    bounded_case16594_general_codes_cv bounded_case16594_source_prefix10
End

Definition bounded_case16594_prefix10_sources_cv_def:
  bounded_case16594_prefix10_sources_cv =
    bounded_case16594_analytic_program_cv bounded_case16594_source_prefix10
End

Definition bounded_case16594_authenticated_fast_packets_cv_def:
  bounded_case16594_authenticated_fast_packets_cv =
    bounded_object_q_cv_list
      (MAP bounded_interval64_object_q_cv
        bounded_case16594_cell0_authenticated_word_runtime_packets)
End

Theorem bounded_case16594_q_equiv_list_left_encoded:
  !left right.
    LIST_REL bounded_case10173_q_cv_equiv left right ==>
    EVERY bounded_object_q_encoded left
Proof
  Induct
  >> Cases_on `right`
  >> simp [LIST_REL_def]
  >> rw
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_case16594_authenticated_object_radii_encoded:
  EVERY bounded_object_q_encoded
    bounded_case16594_cell0_authenticated_object_radii
Proof
  metis_tac
    [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
     bounded_case16594_q_equiv_list_left_encoded]
QED

Theorem bounded_case16594_authenticated_object_boxes_valid:
  EVERY bounded_packed_q_interval_valid_cv
      bounded_case16594_cell0_authenticated_object_center_environment /\
  EVERY bounded_packed_q_interval_valid_cv
      bounded_case16594_cell0_authenticated_object_box_environment
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_object_center_environment_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_object_box_environment_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_authenticated_valid_interval_object_encoded:
  bounded_packed_q_interval_valid_cv value ==>
  bounded_object_q_interval_encoded value
Proof
  rw
    [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> metis_tac []
QED

Theorem bounded_case16594_authenticated_valid_intervals_object_encoded:
  !values.
    EVERY bounded_packed_q_interval_valid_cv values ==>
    EVERY bounded_object_q_interval_encoded values
Proof
  Induct
  >> simp [bounded_case16594_authenticated_valid_interval_object_encoded]
QED

Theorem bounded_case16594_authenticated_object_boxes_equivalent:
  LIST_REL bounded_object_q_interval_cv_equiv
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_center_environment /\
  LIST_REL bounded_object_q_interval_cv_equiv
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_cell0_authenticated_object_box_environment
Proof
  conj_tac
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl
  >> irule bounded_case16594_authenticated_valid_intervals_object_encoded
  >> fs [bounded_case16594_authenticated_object_boxes_valid]
QED

Theorem bounded_case16594_prefix10_general_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_source_prefix10
      bounded_case16594_prepared_prefix10 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_prepared_prefix10 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_source_prefix10 /\
  bounded_case16594_prepared_prefix10 ++
      bounded_case16594_prepared_suffix_after10 =
    bounded_case16594_prepared_program
Proof
  conj_tac
  >- (rw
       [bounded_case16594_source_prefix10_def,
        bounded_case16594_prepared_prefix10_def]
      >> irule LIST_REL_TAKE
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_source_prefix10_def,
        bounded_case16594_prepared_prefix10_def,
        bounded_case16594_prepared_suffix_after10_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_cell0_authenticated_word_runtime_trace_named:
  bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_program
      ([],bounded_case16594_cell0_source_word_certificates) =
    SOME
      (bounded_case16594_cell0_authenticated_word_runtime_final_state,
       bounded_case16594_cell0_authenticated_word_runtime_packets)
Proof
  mp_tac
    (CONJUNCT1
       compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_trace_exact)
  >> simp
       [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_trace_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_radii_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_environment_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_environment_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_box_environment_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_interval64_outward_one_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_certificates_def]
QED

Theorem bounded_case16594_cell0_authenticated_object_prefix0_through9_trace:
  ?word_after10 packets_after10 semantic_after10 runtime_stack_after10.
    bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_suffix_after10 word_after10 =
        SOME
          (bounded_case16594_cell0_authenticated_word_runtime_final_state,
           packets_after10) /\
    bounded_analytic64_state_covers_object_q word_after10 semantic_after10 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after10) packets_after10 /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_source_prefix10
      bounded_case16594_prepared_prefix10
      bounded_case16594_prefix10_codes_cv
      bounded_case16594_prefix10_sources_cv
      bounded_case16594_authenticated_fast_packets_cv
      []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after10)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after10))))
      semantic_after10
Proof
  mp_tac
    (Q.SPECL
      [`bounded_case16594_source_prefix10`,
       `bounded_case16594_prepared_prefix10`,
       `bounded_case16594_prepared_suffix_after10`,
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
  >- (simp
       [bounded_case16594_authenticated_object_radii_encoded,
        compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_payload_lengths,
        compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent,
        bounded_case16594_authenticated_object_boxes_valid,
        bounded_case16594_authenticated_object_boxes_equivalent,
        bounded_case16594_prefix10_general_contract,
        bounded_case16594_cell0_authenticated_word_runtime_trace_named,
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
        bounded_case16594_prefix10_codes_cv_def,
        bounded_case16594_prefix10_sources_cv_def,
        bounded_case16594_authenticated_fast_packets_cv_def]
QED

val _ = export_theory ();
