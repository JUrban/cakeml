(*****************************************************************************
 * Complete arbitrary-state joint trace for the 167-instruction case-16594
 * analytic program.  The only remaining segment after the generic 0--121
 * theorem is the all-ordinary tail at positions 122--166.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointCompleteInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointPrefix122Invariant
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_generic_source_tail122_through166_def:
  bounded_case16594_generic_source_tail122_through166 =
    TAKE 45 (DROP 122 bounded_case16594_program)
End

Definition bounded_case16594_generic_prepared_tail122_through166_def:
  bounded_case16594_generic_prepared_tail122_through166 =
    TAKE 45 (DROP 122 bounded_case16594_prepared_program)
End

Definition bounded_case16594_generic_prepared_suffix_after167_def:
  bounded_case16594_generic_prepared_suffix_after167 =
    DROP 167 bounded_case16594_prepared_program
End

Definition bounded_case16594_generic_source_prefix167_def:
  bounded_case16594_generic_source_prefix167 =
    bounded_case16594_generic_source_prefix122 ++
      bounded_case16594_generic_source_tail122_through166
End

Definition bounded_case16594_generic_prepared_prefix167_def:
  bounded_case16594_generic_prepared_prefix167 =
    bounded_case16594_generic_prepared_prefix122 ++
      bounded_case16594_generic_prepared_tail122_through166
End

Definition bounded_case16594_generic_prefix167_codes_cv_def:
  bounded_case16594_generic_prefix167_codes_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_generic_prefix122_codes_cv
      (bounded_case16594_general_codes_cv
        bounded_case16594_generic_source_tail122_through166)
End

Definition bounded_case16594_generic_prefix167_sources_cv_def:
  bounded_case16594_generic_prefix167_sources_cv =
    bounded_case16594_trace_cv_list_append
      bounded_case16594_generic_prefix122_sources_cv
      (bounded_case16594_analytic_program_cv
        bounded_case16594_generic_source_tail122_through166)
End

Theorem bounded_case16594_generic_tail122_through166_contract:
  LIST_REL (bounded_analytic_instruction_refines 6)
      bounded_case16594_generic_source_tail122_through166
      bounded_case16594_generic_prepared_tail122_through166 /\
  EVERY bounded_analytic64_ordinary_instruction
      bounded_case16594_generic_prepared_tail122_through166 /\
  EVERY bounded_case16594_object_dispatch_source_clock_ok
      bounded_case16594_generic_source_tail122_through166 /\
  bounded_case16594_generic_prepared_tail122_through166 ++
      bounded_case16594_generic_prepared_suffix_after167 =
    bounded_case16594_generic_prepared_suffix_after122
Proof
  conj_tac
  >- (rw
       [bounded_case16594_generic_source_tail122_through166_def,
        bounded_case16594_generic_prepared_tail122_through166_def]
      >> irule LIST_REL_TAKE
      >> irule LIST_REL_DROP
      >> ACCEPT_TAC
           compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines)
  >> simp
       [bounded_case16594_generic_source_tail122_through166_def,
        bounded_case16594_generic_prepared_tail122_through166_def,
        bounded_case16594_generic_prepared_suffix_after167_def,
        compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_prepared_suffix_after122_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_generic_complete_program_identity:
  bounded_case16594_generic_source_prefix167 = bounded_case16594_program /\
  bounded_case16594_generic_prepared_prefix167 =
    bounded_case16594_prepared_program /\
  bounded_case16594_generic_prepared_suffix_after167 = []
Proof
  simp
    [bounded_case16594_generic_source_prefix167_def,
     bounded_case16594_generic_prepared_prefix167_def,
     bounded_case16594_generic_prepared_suffix_after167_def,
     bounded_case16594_generic_source_tail122_through166_def,
     bounded_case16594_generic_prepared_tail122_through166_def,
     compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_source_prefix122_def,
     compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_prepared_prefix122_def,
     compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_source_prefix120_def,
     compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_prepared_prefix120_def,
     compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_source_stretch79_through119_def,
     compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_generic_prepared_stretch79_through119_def,
     compute_boundedCase16594ObjectDispatchJointPrefix79InvariantTheory.bounded_case16594_generic_source_prefix79_def,
     compute_boundedCase16594ObjectDispatchJointPrefix79InvariantTheory.bounded_case16594_generic_prepared_prefix79_def,
     compute_boundedCase16594ObjectDispatchJointPrefix79InvariantTheory.bounded_case16594_generic_source_prefix77_def,
     compute_boundedCase16594ObjectDispatchJointPrefix79InvariantTheory.bounded_case16594_generic_prepared_prefix77_def,
     compute_boundedCase16594ObjectDispatchJointPrefix79InvariantTheory.bounded_case16594_generic_source_stretch36_through76_def,
     compute_boundedCase16594ObjectDispatchJointPrefix79InvariantTheory.bounded_case16594_generic_prepared_stretch36_through76_def,
     compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_generic_source_prefix36_def,
     compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_generic_prepared_prefix36_def,
     compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_generic_source_prefix34_def,
     compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_generic_prepared_prefix34_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_joint_complete_trace:
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
  ?word_after167 packets_after167 semantic_after167 runtime_stack_after167.
    bounded_analytic64_program_runtime_certificate_trace semantic_radii
      word_center_boxes word_outer_boxes
      bounded_case16594_generic_prepared_suffix_after167 word_after167 =
        SOME (final_word_state,packets_after167) /\
    bounded_analytic64_state_covers_object_q word_after167 semantic_after167 /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_after167) packets_after167 /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack_after167
      (FST semantic_after167) /\
    bounded_case16594_object_dispatch_semantic_trace 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      bounded_case16594_generic_source_prefix167
      bounded_case16594_generic_prepared_prefix167
      bounded_case16594_generic_prefix167_codes_cv
      bounded_case16594_generic_prefix167_sources_cv
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packets))
      runtime_stack semantic_state
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack_after167)
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv packets_after167))))
      semantic_after167
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
         compute_boundedCase16594ObjectDispatchJointPrefix122InvariantTheory.bounded_case16594_object_joint_prefix0_through121_trace)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `word_after122`
         (qx_choose_then `packets_after122`
           (qx_choose_then `semantic_after122`
             (qx_choose_then `runtime_stack_after122` strip_assume_tac))))
  >> mp_tac
       (Q.SPECL
         [`bounded_case16594_generic_source_tail122_through166`,
          `bounded_case16594_generic_prepared_tail122_through166`,
          `bounded_case16594_generic_prepared_suffix_after167`,
          `word_after122`, `final_word_state`, `packets_after122`,
          `runtime_stack_after122`, `semantic_after122`]
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
      >> fs [bounded_case16594_generic_tail122_through166_contract])
  >> disch_then
       (qx_choose_then `word_after167`
         (qx_choose_then `packets_after167`
           (qx_choose_then `semantic_after167`
             (qx_choose_then `runtime_stack_after167` strip_assume_tac))))
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after167
        (FST semantic_after167)` by
       metis_tac
         [compute_boundedCase16594ObjectDispatchJointPrefix36InvariantTheory.bounded_case16594_object_named_semantic_trace_final_stack]
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        bounded_case16594_generic_source_prefix167
        bounded_case16594_generic_prepared_prefix167
        bounded_case16594_generic_prefix167_codes_cv
        bounded_case16594_generic_prefix167_sources_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packets))
        runtime_stack semantic_state
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list runtime_stack_after167)
            (bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packets_after167))))
        semantic_after167` by
       (rw
          [bounded_case16594_generic_source_prefix167_def,
           bounded_case16594_generic_prepared_prefix167_def,
           bounded_case16594_generic_prefix167_codes_cv_def,
           bounded_case16594_generic_prefix167_sources_cv_def]
        >> irule
             compute_boundedCase16594ObjectDispatchSemanticTraceAppendTheory.bounded_case16594_object_dispatch_semantic_trace_append
        >> qexists_tac
             `bounded_object_q_cv_list
                (MAP bounded_interval64_object_q_cv packets_after122)`
        >> qexists_tac `runtime_stack_after122`
        >> qexists_tac `semantic_after122`
        >> asm_rewrite_tac [])
  >> qexists_tac `word_after167`
  >> qexists_tac `packets_after167`
  >> qexists_tac `semantic_after167`
  >> qexists_tac `runtime_stack_after167`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
