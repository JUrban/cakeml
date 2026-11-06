(*****************************************************************************
 * Arbitrary-state joint trace through case-16594 instruction 78.
 *
 * Extend the generic 0--35 trace across the ordinary positions 36--76 and
 * the second specialized pair at 77--78.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointPrefix79Invariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointPrefix36Invariant
  compute_boundedCase16594ObjectDispatchJointSecondSpecializedPairInvariant
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_generic_source_stretch36_through76_def:
  bounded_case16594_generic_source_stretch36_through76 =
    TAKE 41 (DROP 36 bounded_case16594_program)
End

Definition bounded_case16594_generic_prepared_stretch36_through76_def:
  bounded_case16594_generic_prepared_stretch36_through76 =
    TAKE 41 (DROP 36 bounded_case16594_prepared_program)
End

Definition bounded_case16594_generic_prepared_suffix_after77_def:
  bounded_case16594_generic_prepared_suffix_after77 =
    DROP 77 bounded_case16594_prepared_program
End

Definition bounded_case16594_generic_prepared_suffix_after79_def:
  bounded_case16594_generic_prepared_suffix_after79 =
    DROP 79 bounded_case16594_prepared_program
End

Definition bounded_case16594_generic_source_prefix77_def:
  bounded_case16594_generic_source_prefix77 =
    bounded_case16594_generic_source_prefix36 ++
      bounded_case16594_generic_source_stretch36_through76
End

Definition bounded_case16594_generic_prepared_prefix77_def:
  bounded_case16594_generic_prepared_prefix77 =
    bounded_case16594_generic_prepared_prefix36 ++
      bounded_case16594_generic_prepared_stretch36_through76
End

Definition bounded_case16594_generic_prefix77_codes_cv_def:
  bounded_case16594_generic_prefix77_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_generic_prefix36_codes_cv
      (bounded_case16594_general_codes_cv
        bounded_case16594_generic_source_stretch36_through76)
End

Definition bounded_case16594_generic_prefix77_sources_cv_def:
  bounded_case16594_generic_prefix77_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_generic_prefix36_sources_cv
      (bounded_case16594_analytic_program_cv
        bounded_case16594_generic_source_stretch36_through76)
End

Definition bounded_case16594_generic_source_prefix79_def:
  bounded_case16594_generic_source_prefix79 =
    bounded_case16594_generic_source_prefix77 ++
      [EL 77 bounded_case16594_program;EL 78 bounded_case16594_program]
End

Definition bounded_case16594_generic_prepared_prefix79_def:
  bounded_case16594_generic_prepared_prefix79 =
    bounded_case16594_generic_prepared_prefix77 ++
      [BoundedAnalytic64NegDeltaDerivative 4;
       BoundedAnalytic64FourCoordinateDelta 1]
End

Definition bounded_case16594_generic_prefix79_codes_cv_def:
  bounded_case16594_generic_prefix79_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_generic_prefix77_codes_cv
      (Pair (Num 5) (Pair (Num 2) (Num 0)))
End

Definition bounded_case16594_generic_prefix79_sources_cv_def:
  bounded_case16594_generic_prefix79_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_generic_prefix77_sources_cv
      (Pair bounded_case16594_object_source77_cv
        (Pair bounded_case16594_object_source78_cv (Num 0)))
End

Theorem bounded_case16594_generic_stretch36_through76_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_generic_source_stretch36_through76
      bounded_case16594_generic_prepared_stretch36_through76 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_generic_prepared_stretch36_through76 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_generic_source_stretch36_through76 /\
  bounded_case16594_generic_prepared_stretch36_through76 ++
      bounded_case16594_generic_prepared_suffix_after77 =
    bounded_case16594_generic_prepared_suffix_after36 /\
  bounded_case16594_generic_prepared_suffix_after77 =
    BoundedAnalytic64NegDeltaDerivative 4 ::
    BoundedAnalytic64FourCoordinateDelta 1 ::
    bounded_case16594_generic_prepared_suffix_after79
Proof
  conj_tac
  >- (rw
       [bounded_case16594_generic_source_stretch36_through76_def,
        bounded_case16594_generic_prepared_stretch36_through76_def]
      >> irule LIST_REL_TAKE
      >> irule LIST_REL_DROP
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_generic_source_stretch36_through76_def,
        bounded_case16594_generic_prepared_stretch36_through76_def,
        bounded_case16594_generic_prepared_suffix_after77_def,
        bounded_case16594_generic_prepared_suffix_after79_def,
        compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_generic_prepared_suffix_after36_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_object_joint_prefix0_through78_trace:
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
  ?word_after79 packets_after79 semantic_after79 runtime_stack_after79.
    bounded_analytic64_program_runtime_certificate_trace semantic_radii
      word_center_boxes word_outer_boxes
      bounded_case16594_generic_prepared_suffix_after79 word_after79 =
        SOME (final_word_state,packets_after79) /\
    bounded_analytic64_state_covers_object_q word_after79 semantic_after79 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after79) packets_after79 /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack_after79
      (FST semantic_after79) /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      bounded_case16594_generic_source_prefix79
      bounded_case16594_generic_prepared_prefix79
      bounded_case16594_generic_prefix79_codes_cv
      bounded_case16594_generic_prefix79_sources_cv
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packets))
      runtime_stack semantic_state
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after79)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after79))))
      semantic_after79
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `word_state` |-> `word_state`,
          `final_word_state` |-> `final_word_state`,
          `packets` |-> `packets`, `semantic_state` |-> `semantic_state`,
          `runtime_stack` |-> `runtime_stack`]
         compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_object_joint_prefix0_through35_trace)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `word_after36`
         (qx_choose_then `packets_after36`
           (qx_choose_then `semantic_after36`
             (qx_choose_then `runtime_stack_after36` strip_assume_tac))))
  >> mp_tac
       (Q.SPECL
         [`bounded_case16594_generic_source_stretch36_through76`,
          `bounded_case16594_generic_prepared_stretch36_through76`,
          `bounded_case16594_generic_prepared_suffix_after77`,
          `word_after36`, `final_word_state`, `packets_after36`,
          `runtime_stack_after36`, `semantic_after36`]
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
      >> fs [bounded_case16594_generic_stretch36_through76_contract])
  >> disch_then
       (qx_choose_then `word_after77`
         (qx_choose_then `packets_after77`
           (qx_choose_then `semantic_after77`
             (qx_choose_then `runtime_stack_after77` strip_assume_tac))))
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after77
        (FST semantic_after77)` by
       metis_tac
         [compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_object_named_semantic_trace_final_stack]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `prepared_suffix` |->
            `bounded_case16594_generic_prepared_suffix_after79`,
          `word_state` |-> `word_after77`,
          `final_word_state` |-> `final_word_state`,
          `packets` |-> `packets_after77`,
          `semantic_state` |-> `semantic_after77`,
          `runtime_stack` |-> `runtime_stack_after77`]
         compute_boundedCase16594ObjectDispatchJointSecondSpecializedPairInvariantTheory.bounded_case16594_object_joint_second_specialized_pair_trace)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs [bounded_case16594_generic_stretch36_through76_contract])
  >> disch_then
       (qx_choose_then `word_after79`
         (qx_choose_then `packets_after79`
           (qx_choose_then `semantic_after79`
             (qx_choose_then `runtime_stack_after79` strip_assume_tac))))
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after79
        (FST semantic_after79)` by
       metis_tac
         [compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_object_named_semantic_trace_final_stack]
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        bounded_case16594_generic_source_prefix77
        bounded_case16594_generic_prepared_prefix77
        bounded_case16594_generic_prefix77_codes_cv
        bounded_case16594_generic_prefix77_sources_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after77)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after77))))
        semantic_after77` by
       (rw
          [bounded_case16594_generic_source_prefix77_def,
           bounded_case16594_generic_prepared_prefix77_def,
           bounded_case16594_generic_prefix77_codes_cv_def,
           bounded_case16594_generic_prefix77_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after36)`
        >> qexists_tac `runtime_stack_after36`
        >> qexists_tac `semantic_after36`
        >> asm_rewrite_tac [])
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        bounded_case16594_generic_source_prefix79
        bounded_case16594_generic_prepared_prefix79
        bounded_case16594_generic_prefix79_codes_cv
        bounded_case16594_generic_prefix79_sources_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after79)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after79))))
        semantic_after79` by
       (rw
          [bounded_case16594_generic_source_prefix79_def,
           bounded_case16594_generic_prepared_prefix79_def,
           bounded_case16594_generic_prefix79_codes_cv_def,
           bounded_case16594_generic_prefix79_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after77)`
        >> qexists_tac `runtime_stack_after77`
        >> qexists_tac `semantic_after77`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after79`
  >> qexists_tac `packets_after79`
  >> qexists_tac `semantic_after79`
  >> qexists_tac `runtime_stack_after79`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
