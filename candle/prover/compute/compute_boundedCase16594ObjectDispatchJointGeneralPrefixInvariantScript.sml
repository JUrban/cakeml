(*****************************************************************************
 * Joint authenticated trace for an all-general prefix.
 *
 * The fixed-word runtime trace is the numerical authority for each step and
 * for the exact flat certificate packet.  The packet contract is consumed in
 * lockstep, while the general-code joint step supplies both the object-q
 * semantic successor and the production evaluator successor.  Stopping at a
 * prefix deliberately preserves the untouched word state, certificate packet
 * suffix, semantic state, and production runtime state for the next packet.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointGeneralCodeStepInvariant
  compute_boundedCase16594ObjectDispatchSemanticTrace
  compute_boundedCase16594ObjectDispatchCanonicalSourceIdentity
Libs
  bossLib preamble intLib

Definition bounded_case16594_general_codes_cv_def:
  bounded_case16594_general_codes_cv program =
    FOLDR (\instruction rest. Pair (Num 0) rest) (Num 0:cv) program
End

Definition bounded_case16594_object_dispatch_source_clock_ok_def:
  bounded_case16594_object_dispatch_source_clock_ok source <=>
    case source of
    | BoundedAnalyticPolynomial source_program =>
        4105 + LENGTH source_program <= 524405
    | _ => T
End

Theorem bounded_case16594_object_joint_general_prefix_trace:
  !source_prefix prepared_prefix prepared_suffix word_state final_word_state
   packets runtime_stack semantic_state.
    EVERY bounded_object_q_encoded runtime_radii /\
    LENGTH runtime_radii = 6 /\
    bounded_taylor_radius_pairs semantic_radii = SOME weights /\
    LIST_REL bounded_case10173_q_cv_equiv runtime_radii
      (MAP bounded_word64_object_q_cv semantic_radii) /\
    LENGTH runtime_center_box_values = 6 /\
    LENGTH runtime_outer_box_values = 6 /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_center_box_values semantic_center_boxes /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_outer_box_values semantic_outer_boxes /\
    EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
    EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
    LIST_REL (bounded_analytic_instruction_refines 6)
      source_prefix prepared_prefix /\
    EVERY bounded_analytic64_ordinary_instruction prepared_prefix /\
    EVERY bounded_case16594_object_dispatch_source_clock_ok source_prefix /\
    bounded_analytic64_program_runtime_certificate_trace semantic_radii
      word_center_boxes word_outer_boxes (prepared_prefix ++ prepared_suffix)
      word_state = SOME (final_word_state,packets) /\
    bounded_analytic64_state_covers_object_q word_state semantic_state /\
    LIST_REL bounded_interval64_covers_object_q
      word_center_boxes semantic_center_boxes /\
    LIST_REL bounded_interval64_covers_object_q
      word_outer_boxes semantic_outer_boxes /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_state) packets /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack
      (FST semantic_state)
    ==>
    ?word_middle packets_remaining semantic_middle runtime_stack_middle.
      bounded_analytic64_program_runtime_certificate_trace semantic_radii
        word_center_boxes word_outer_boxes prepared_suffix word_middle =
          SOME (final_word_state,packets_remaining) /\
      bounded_analytic64_state_covers_object_q word_middle semantic_middle /\
      bounded_case16594_word_dispatch_packet_contracts
        (SND word_middle) packets_remaining /\
      bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list runtime_center_box_values)
        (bounded_object_q_cv_list runtime_outer_box_values)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        source_prefix prepared_prefix
        (bounded_case16594_general_codes_cv source_prefix)
        (bounded_case16594_analytic_program_cv source_prefix)
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_middle)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_remaining))))
        semantic_middle
Proof
  Induct_on `source_prefix`
  >- (rpt gen_tac
      >> Cases_on `prepared_prefix`
      >> simp
           [bounded_case16594_general_codes_cv_def,
            compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_program_cv_def,
            compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def]
      >> rpt strip_tac
      >> qexists_tac `word_state`
      >> qexists_tac `packets`
      >> qexists_tac `runtime_stack`
      >> asm_rewrite_tac [])
  >> rpt gen_tac
  >> Cases_on `prepared_prefix`
  >- simp []
  >> strip_tac
  >> fs [LIST_REL_def]
  >> drule
       compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_cons
  >> disch_then
       (qx_choose_then `packet`
         (qx_choose_then `word_next`
           (qx_choose_then `rest_packets` strip_assume_tac)))
  >> mp_tac
       (Q.INST
         [`source` |-> `h`, `prepared` |-> `h'`,
          `word_state` |-> `word_state`, `word_next` |-> `word_next`,
          `packet` |-> `packet`, `packet_rest` |-> `rest_packets`,
          `runtime_stack` |-> `runtime_stack`,
          `runtime_radii` |-> `runtime_radii`,
          `runtime_center_box_values` |-> `runtime_center_box_values`,
          `runtime_outer_box_values` |-> `runtime_outer_box_values`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `semantic_state` |-> `semantic_state`]
         compute_boundedCase16594ObjectDispatchJointGeneralCodeStepInvariantTheory.bounded_case16594_object_joint_general_code_step_eval_above)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [bounded_case16594_object_dispatch_source_clock_ok_def])
  >> disch_then
       (qx_choose_then `semantic_next`
         (qx_choose_then `next_runtime_stack` strip_assume_tac))
  >> first_x_assum
       (mp_tac o Q.SPECL
         [`t`, `prepared_suffix`, `word_next`, `final_word_state`,
          `rest_packets`, `next_runtime_stack`, `semantic_next`])
  >> impl_tac
  >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `word_middle`
         (qx_choose_then `packets_remaining`
           (qx_choose_then `semantic_middle`
             (qx_choose_then `runtime_stack_middle` strip_assume_tac))))
  >> qexists_tac `word_middle`
  >> qexists_tac `packets_remaining`
  >> qexists_tac `semantic_middle`
  >> qexists_tac `runtime_stack_middle`
  >> asm_rewrite_tac []
  >> simp
       [bounded_case16594_general_codes_cv_def,
        compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_program_cv_def,
        compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_instruction_cv_round_trip,
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def]
  >> qexists_tac
       `bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv rest_packets)`
  >> qexists_tac `next_runtime_stack`
  >> qexists_tac `semantic_next`
  >> asm_rewrite_tac []
  >> simp [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> fs
       [bounded_case16594_general_codes_cv_def,
        compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_program_cv_def,
        MAP_APPEND,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

val _ = export_theory ();
