(*****************************************************************************
 * Stack-level adapters for the second authenticated specialized pair under
 * production runtime radii (positions 77 and 78).
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSecondSpecializedRuntimeDispatchInvariant
Ancestors
  compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_neg4_dispatch_runtime_radii_refines:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes 4 /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 262502
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 5) bounded_case16594_object_source77_cv certificates
      (bounded_object_q_cv_list runtime_stack)
      (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
      certificates /\
    bounded_object_q_analytic_step semantic_radii weights center_boxes
      outer_boxes (EL 77 bounded_case16594_program)
      (BoundedAnalytic64NegDeltaDerivative 4)
      (semantic_stack,semantic_certificates)
      (object_result::semantic_stack,semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (object_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `coordinate` |-> `4`]
         compute_boundedCase16594ObjectSpecializedRuntimeRadiiInvariantTheory.bounded_case16594_object_delta_neg_runtime_radii_eval_above_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_neg_source_state_cv
          runtime_radii center_boxes 4`
  >> qexists_tac `object_result`
  >> conj_tac
  >- (irule
        (SIMP_RULE arith_ss []
          (Q.INST [`numeric_floor` |-> `262500`]
            compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_neg4_eval_above))
      >> fs [compute_execTheory.from_cv_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source77_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_product1_dispatch_runtime_radii_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes 1 /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 2) bounded_case16594_object_source78_cv certificates
      (bounded_object_q_cv_list runtime_stack)
      (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
      certificates /\
    bounded_object_q_analytic_step semantic_radii weights center_boxes
      outer_boxes (EL 78 bounded_case16594_program)
      (BoundedAnalytic64FourCoordinateDelta 1)
      (semantic_stack,semantic_certificates)
      (object_result::semantic_stack,semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (object_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `outer_boxes` |-> `outer_boxes`,
          `coordinate` |-> `1`]
         compute_boundedCase16594ObjectSpecializedRuntimeRadiiInvariantTheory.bounded_case16594_object_delta_product_runtime_radii_eval_above_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_product_source_state_cv
          runtime_radii center_boxes outer_boxes 1`
  >> qexists_tac `object_result`
  >> conj_tac
  >- (irule
        (SIMP_RULE arith_ss []
          (Q.INST [`numeric_floor` |-> `524403`]
            compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_product1_eval_above))
      >> fs [compute_execTheory.from_cv_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source78_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_neg4_packet_state:
  bounded_analytic64_runtime_certificate_packet
      (BoundedAnalytic64NegDeltaDerivative 4) word_state = SOME packet /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
      word_outer_boxes (BoundedAnalytic64NegDeltaDerivative 4) word_state =
    SOME word_next
  ==>
  packet = [] /\ SND word_next = SND word_state
Proof
  Cases_on `word_state`
  >> simp
       [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
        compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> rpt strip_tac
  >> gvs
       [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def]
QED

Theorem bounded_case16594_product1_packet_state:
  bounded_analytic64_runtime_certificate_packet
      (BoundedAnalytic64FourCoordinateDelta 1) word_state = SOME packet /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
      word_outer_boxes (BoundedAnalytic64FourCoordinateDelta 1) word_state =
    SOME word_next
  ==>
  packet = [] /\ SND word_next = SND word_state
Proof
  Cases_on `word_state`
  >> simp
       [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def,
        compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> rpt strip_tac
  >> gvs
       [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def]
QED

Theorem bounded_case16594_object_joint_neg4_runtime_step:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights semantic_center_boxes 4 /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes (BoundedAnalytic64NegDeltaDerivative 4) word_state =
      SOME word_next /\
  bounded_case16594_word_dispatch_packet_contracts
    (SND word_state) packet_rest /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes
      (EL 77 bounded_case16594_program)
      (BoundedAnalytic64NegDeltaDerivative 4)
      semantic_state semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 5) bounded_case16594_object_source77_cv
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packet_rest))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packet_rest)) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = SND word_next /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_next) packet_rest
Proof
  strip_tac
  >> Cases_on `semantic_state`
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `semantic_center_boxes`,
          `outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_stack` |-> `runtime_stack`, `semantic_stack` |-> `q`,
          `semantic_certificates` |-> `r`,
          `certificates` |->
            `bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packet_rest)`]
         bounded_case16594_object_neg4_dispatch_runtime_radii_refines)
  >> impl_tac >- fs []
  >> disch_then
       (qx_choose_then `runtime_result`
         (qx_choose_then `object_result` strip_assume_tac))
  >> mp_tac
       (Q.INST
         [`source` |-> `EL 77 bounded_case16594_program`,
          `coordinate` |-> `4`,
          `word_state` |-> `word_state`, `object_state` |-> `(q,r)`,
          `word_next` |-> `word_next`, `radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `center_environment` |-> `word_center_boxes`,
          `box_environment` |-> `word_outer_boxes`,
          `object_center_environment` |-> `semantic_center_boxes`,
          `object_box_environment` |-> `semantic_outer_boxes`]
         compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_analytic64_neg_delta_dispatch_refines_object_q)
  >> impl_tac
  >- fs
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source77_specialization_ok,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_neg_refinement_context_def]
  >> disch_then (qx_choose_then `object_next` strip_assume_tac)
  >> fs
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source77_specialization_ok]
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        (Num 5) bounded_case16594_object_source77_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packet_rest))
        (bounded_object_q_cv_list runtime_stack)
        (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv packet_rest))` by
       (irule
          (Q.INST [`lower` |-> `262502`, `upper` |-> `524405`]
            compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken)
        >> simp [])
  >> `SND word_next = SND word_state` by
       (Cases_on `word_state`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> qexists_tac `runtime_result::runtime_stack`
  >> Cases_on `word_state`
  >> gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_object_joint_product1_runtime_step:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights semantic_center_boxes semantic_outer_boxes 1 /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes (BoundedAnalytic64FourCoordinateDelta 1) word_state =
      SOME word_next /\
  bounded_case16594_word_dispatch_packet_contracts
    (SND word_state) packet_rest /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes
      (EL 78 bounded_case16594_program)
      (BoundedAnalytic64FourCoordinateDelta 1)
      semantic_state semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 2) bounded_case16594_object_source78_cv
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packet_rest))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packet_rest)) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = SND word_next /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND word_next) packet_rest
Proof
  strip_tac
  >> Cases_on `semantic_state`
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `semantic_center_boxes`,
          `outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_stack` |-> `runtime_stack`, `semantic_stack` |-> `q`,
          `semantic_certificates` |-> `r`,
          `certificates` |->
            `bounded_object_q_cv_list
              (MAP bounded_interval64_object_q_cv packet_rest)`]
         bounded_case16594_object_product1_dispatch_runtime_radii_refines)
  >> impl_tac >- fs []
  >> disch_then
       (qx_choose_then `runtime_result`
         (qx_choose_then `object_result` strip_assume_tac))
  >> mp_tac
       (Q.INST
         [`source` |-> `EL 78 bounded_case16594_program`,
          `coordinate` |-> `1`,
          `word_state` |-> `word_state`, `object_state` |-> `(q,r)`,
          `word_next` |-> `word_next`, `radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `center_environment` |-> `word_center_boxes`,
          `box_environment` |-> `word_outer_boxes`,
          `object_center_environment` |-> `semantic_center_boxes`,
          `object_box_environment` |-> `semantic_outer_boxes`]
         compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_analytic64_four_coordinate_dispatch_refines_object_q)
  >> impl_tac
  >- fs
       [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source78_specialization_ok,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_product_refinement_context_def]
  >> disch_then (qx_choose_then `object_next` strip_assume_tac)
  >> fs
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source78_specialization_ok]
  >> `SND word_next = SND word_state` by
       (Cases_on `word_state`
        >> fs
             [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
        >> every_case_tac
        >> gvs [])
  >> qexists_tac `runtime_result::runtime_stack`
  >> Cases_on `word_state`
  >> gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

val _ = export_theory ();
