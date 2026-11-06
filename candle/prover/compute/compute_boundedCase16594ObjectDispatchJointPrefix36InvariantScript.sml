(*****************************************************************************
 * Arbitrary-state joint trace through case-16594 instruction 35.
 *
 * This composes the generic all-ordinary induction for positions 0--33 with
 * the reusable specialized splice for positions 34--35.  The result is the
 * first non-concrete prefix of the complete 167-step G3f trace.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointPrefix36Invariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointFirstSpecializedPairInvariant
  compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariant
  compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_generic_source_prefix34_def:
  bounded_case16594_generic_source_prefix34 =
    TAKE 34 bounded_case16594_program
End

Definition bounded_case16594_generic_prepared_prefix34_def:
  bounded_case16594_generic_prepared_prefix34 =
    TAKE 34 bounded_case16594_prepared_program
End

Definition bounded_case16594_generic_prepared_suffix_after34_def:
  bounded_case16594_generic_prepared_suffix_after34 =
    DROP 34 bounded_case16594_prepared_program
End

Definition bounded_case16594_generic_prepared_suffix_after36_def:
  bounded_case16594_generic_prepared_suffix_after36 =
    DROP 36 bounded_case16594_prepared_program
End

Definition bounded_case16594_generic_source_prefix36_def:
  bounded_case16594_generic_source_prefix36 =
    bounded_case16594_generic_source_prefix34 ++
      [EL 34 bounded_case16594_program;EL 35 bounded_case16594_program]
End

Definition bounded_case16594_generic_prepared_prefix36_def:
  bounded_case16594_generic_prepared_prefix36 =
    bounded_case16594_generic_prepared_prefix34 ++
      [BoundedAnalytic64NegDeltaDerivative 3;
       BoundedAnalytic64FourCoordinateDelta 0]
End

Definition bounded_case16594_generic_prefix36_codes_cv_def:
  bounded_case16594_generic_prefix36_codes_cv =
    bounded_case16594_trace_cv_list_append
      (bounded_case16594_general_codes_cv
        bounded_case16594_generic_source_prefix34)
      (Pair (Num 4) (Pair (Num 1) (Num 0)))
End

Definition bounded_case16594_generic_prefix36_sources_cv_def:
  bounded_case16594_generic_prefix36_sources_cv =
    bounded_case16594_trace_cv_list_append
      (bounded_case16594_analytic_program_cv
        bounded_case16594_generic_source_prefix34)
      (Pair bounded_case16594_object_source34_cv
        (Pair bounded_case16594_object_source35_cv (Num 0)))
End

Theorem bounded_case16594_generic_prefix34_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_generic_source_prefix34
      bounded_case16594_generic_prepared_prefix34 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_generic_prepared_prefix34 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_generic_source_prefix34 /\
  bounded_case16594_generic_prepared_prefix34 ++
      bounded_case16594_generic_prepared_suffix_after34 =
    bounded_case16594_prepared_program /\
  bounded_case16594_generic_prepared_suffix_after34 =
    BoundedAnalytic64NegDeltaDerivative 3 ::
    BoundedAnalytic64FourCoordinateDelta 0 ::
    bounded_case16594_generic_prepared_suffix_after36
Proof
  conj_tac
  >- (rw
       [bounded_case16594_generic_source_prefix34_def,
        bounded_case16594_generic_prepared_prefix34_def]
      >> irule LIST_REL_TAKE
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_generic_source_prefix34_def,
        bounded_case16594_generic_prepared_prefix34_def,
        bounded_case16594_generic_prepared_suffix_after34_def,
        bounded_case16594_generic_prepared_suffix_after36_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_object_named_semantic_trace_final_stack:
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

Theorem bounded_case16594_object_joint_prefix0_through35_trace:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LENGTH semantic_center_boxes = 6 /\
  LENGTH semantic_outer_boxes = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    semantic_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    semantic_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_runtime_certificate_trace semantic_radii
    word_center_boxes word_outer_boxes bounded_case16594_prepared_program
    word_state = SOME (final_word_state,packets) /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  bounded_case16594_word_dispatch_packet_contracts
    (SND word_state) packets /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state)
  ==>
  ?word_after36 packets_after36 semantic_after36 runtime_stack_after36.
    bounded_analytic64_program_runtime_certificate_trace semantic_radii
      word_center_boxes word_outer_boxes
      bounded_case16594_generic_prepared_suffix_after36 word_after36 =
        SOME (final_word_state,packets_after36) /\
    bounded_analytic64_state_covers_object_q word_after36 semantic_after36 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after36) packets_after36 /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack_after36
      (FST semantic_after36) /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      bounded_case16594_generic_source_prefix36
      bounded_case16594_generic_prepared_prefix36
      bounded_case16594_generic_prefix36_codes_cv
      bounded_case16594_generic_prefix36_sources_cv
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packets))
      runtime_stack semantic_state
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after36)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after36))))
      semantic_after36
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`bounded_case16594_generic_source_prefix34`,
          `bounded_case16594_generic_prepared_prefix34`,
          `bounded_case16594_generic_prepared_suffix_after34`,
          `word_state`, `final_word_state`, `packets`, `runtime_stack`,
          `semantic_state`]
         (Q.INST
           [`runtime_radii` |-> `runtime_radii`,
            `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
            `runtime_center_box_values` |-> `semantic_center_boxes`,
            `runtime_outer_box_values` |-> `semantic_outer_boxes`,
            `semantic_center_boxes` |-> `semantic_center_boxes`,
            `semantic_outer_boxes` |-> `semantic_outer_boxes`,
            `word_center_boxes` |-> `word_center_boxes`,
            `word_outer_boxes` |-> `word_outer_boxes`]
           compute_boundedCase16594ObjectDispatchJointGeneralPrefixInvariantTheory.bounded_case16594_object_joint_general_prefix_trace))
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs [bounded_case16594_generic_prefix34_contract])
  >> disch_then
       (qx_choose_then `word_after34`
         (qx_choose_then `packets_after34`
           (qx_choose_then `semantic_after34`
             (qx_choose_then `runtime_stack_after34` strip_assume_tac))))
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after34
        (FST semantic_after34)` by
       metis_tac [bounded_case16594_object_named_semantic_trace_final_stack]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `prepared_suffix` |->
            `bounded_case16594_generic_prepared_suffix_after36`,
          `word_state` |-> `word_after34`,
          `final_word_state` |-> `final_word_state`,
          `packets` |-> `packets_after34`,
          `semantic_state` |-> `semantic_after34`,
          `runtime_stack` |-> `runtime_stack_after34`]
         compute_boundedCase16594ObjectDispatchJointFirstSpecializedPairInvariantTheory.bounded_case16594_object_joint_first_specialized_pair_trace)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs [bounded_case16594_generic_prefix34_contract])
  >> disch_then
       (qx_choose_then `word_after36`
         (qx_choose_then `packets_after36`
           (qx_choose_then `semantic_after36`
             (qx_choose_then `runtime_stack_after36` strip_assume_tac))))
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after36
        (FST semantic_after36)` by
       metis_tac [bounded_case16594_object_named_semantic_trace_final_stack]
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        bounded_case16594_generic_source_prefix36
        bounded_case16594_generic_prepared_prefix36
        bounded_case16594_generic_prefix36_codes_cv
        bounded_case16594_generic_prefix36_sources_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after36)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after36))))
        semantic_after36` by
       (rw
          [bounded_case16594_generic_source_prefix36_def,
           bounded_case16594_generic_prepared_prefix36_def,
           bounded_case16594_generic_prefix36_codes_cv_def,
           bounded_case16594_generic_prefix36_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after34)`
        >> qexists_tac `runtime_stack_after34`
        >> qexists_tac `semantic_after34`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after36`
  >> qexists_tac `packets_after36`
  >> qexists_tac `semantic_after36`
  >> qexists_tac `runtime_stack_after36`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
