(*****************************************************************************
 * Stack-level adapters for the first authenticated specialized pair under
 * production runtime radii.
 *
 * Positions 34 and 35 are the first point where the all-general prefix hands
 * its exact-rational runtime radii to a specialized delta evaluator.  The
 * semantic radii remain the authenticated fixed-word values.  These theorems
 * join the generic runtime-radii transport with the exact source/code guards.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectFirstSpecializedRuntimeDispatchInvariant
Ancestors
  compute_boundedCase16594ObjectSpecializedRuntimeRadiiInvariant
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594ObjectDispatchSemanticTrace
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_neg3_dispatch_runtime_radii_refines:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes 3 /\
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
      (Num 4) bounded_case16594_object_source34_cv certificates
      (bounded_object_q_cv_list runtime_stack)
      (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
      certificates /\
    bounded_object_q_analytic_step semantic_radii weights center_boxes
      outer_boxes (EL 34 bounded_case16594_program)
      (BoundedAnalytic64NegDeltaDerivative 3)
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
          `center_boxes` |-> `center_boxes`, `coordinate` |-> `3`]
         compute_boundedCase16594ObjectSpecializedRuntimeRadiiInvariantTheory.bounded_case16594_object_delta_neg_runtime_radii_eval_above_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_neg_source_state_cv
          runtime_radii center_boxes 3`
  >> qexists_tac `object_result`
  >> conj_tac
  >- (irule
        (SIMP_RULE arith_ss []
          (Q.INST [`numeric_floor` |-> `262500`]
            compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_neg3_eval_above))
      >> fs [compute_execTheory.from_cv_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source34_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_product0_dispatch_runtime_radii_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes 0 /\
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
      (Num 1) bounded_case16594_object_source35_cv certificates
      (bounded_object_q_cv_list runtime_stack)
      (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
      certificates /\
    bounded_object_q_analytic_step semantic_radii weights center_boxes
      outer_boxes (EL 35 bounded_case16594_program)
      (BoundedAnalytic64FourCoordinateDelta 0)
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
          `coordinate` |-> `0`]
         compute_boundedCase16594ObjectSpecializedRuntimeRadiiInvariantTheory.bounded_case16594_object_delta_product_runtime_radii_eval_above_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_product_source_state_cv
          runtime_radii center_boxes outer_boxes 0`
  >> qexists_tac `object_result`
  >> conj_tac
  >- (irule
        (SIMP_RULE arith_ss []
          (Q.INST [`numeric_floor` |-> `524403`]
            compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_product0_eval_above))
      >> fs [compute_execTheory.from_cv_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source35_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_neg3_packet_state:
  bounded_analytic64_runtime_certificate_packet
      (BoundedAnalytic64NegDeltaDerivative 3) word_state = SOME packet /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
      word_outer_boxes (BoundedAnalytic64NegDeltaDerivative 3) word_state =
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

Theorem bounded_case16594_product0_packet_state:
  bounded_analytic64_runtime_certificate_packet
      (BoundedAnalytic64FourCoordinateDelta 0) word_state = SOME packet /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
      word_outer_boxes (BoundedAnalytic64FourCoordinateDelta 0) word_state =
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

Theorem bounded_case16594_object_delta_neg_refinement_context_from_word:
  coordinate < 6 /\
  LENGTH object_center_environment = 6 /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_environment object_center_environment /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  bounded_delta64_neg_derivative semantic_radii word_center_environment
    coordinate = SOME word_result
  ==>
  bounded_case16594_object_delta_neg_refinement_context
    semantic_radii weights object_center_environment coordinate
Proof
  strip_tac
  >> drule_all
       compute_boundedAnalyticObjectDeltaNegDerivativeRefinementTheory.bounded_delta64_neg_derivative_covers_object_q
  >> strip_tac
  >> `bounded_object_q_delta_neg_derivative_cv semantic_radii
        object_center_environment coordinate =
      SOME
        (bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_neg_center_value_environment_cv
            object_center_environment coordinate)
          (bounded_case16594_object_delta_neg_center_gradient_environment_cv
            object_center_environment coordinate)
          (bounded_case16594_object_delta_neg_hessian_six_list_cv
            coordinate))` by
       (irule
          compute_boundedCase16594ObjectDeltaNegRefinementBridgeTheory.bounded_case16594_object_delta_neg_semantic_environment
        >> simp [])
  >> gvs []
  >> `EVERY bounded_packed_q_interval_valid_cv object_center_environment` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_neg_center_value_environment_cv
          object_center_environment coordinate) /\
      EVERY bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          object_center_environment coordinate) /\
      EVERY bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate)` by
       (Cases_on `word_result`
        >> fs
             [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
              compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def,
              compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def]
        >> metis_tac
             [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_covers_packed_q_interval_valid_cv,
              compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv])
  >> `EVERY bounded_packed_q_interval_encoded object_center_environment` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded]
  >> `EVERY bounded_packed_q_interval_encoded
        [EL 0 object_center_environment;EL 1 object_center_environment;
         EL 2 object_center_environment;EL 3 object_center_environment;
         EL 4 object_center_environment;EL 5 object_center_environment]` by
       fs [listTheory.EVERY_EL]
  >> `LENGTH
        (bounded_case16594_object_delta_neg_center_gradient_environment_cv
          object_center_environment coordinate) = 6` by
       (PURE_REWRITE_TAC
          [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_gradient_environment_cv_def]
        >> metis_tac
             [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_components_encoded])
  >> `LENGTH
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) =
      21` by
       simp
         [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_hessian_six_encoded_length]
  >> simp
       [compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_neg_refinement_context_def]
QED

Theorem bounded_case16594_object_delta_product_refinement_context_from_word:
  coordinate < 6 /\
  LENGTH object_center_environment = 6 /\
  LENGTH object_outer_environment = 6 /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_environment object_outer_environment /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  bounded_delta64_four_coordinate semantic_radii word_center_environment
    word_outer_environment coordinate = SOME word_result
  ==>
  bounded_case16594_object_delta_product_refinement_context
    semantic_radii weights object_center_environment object_outer_environment
    coordinate
Proof
  strip_tac
  >> drule
       compute_boundedAnalyticObjectDeltaFourCoordinateRefinementTheory.bounded_delta64_four_coordinate_trace
  >> strip_tac
  >> drule_all
       compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_delta64_value_covers_object_q
  >> strip_tac
  >> drule_all
       compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_delta64_pair_products_covers_object_q
  >> strip_tac
  >> drule_all
       compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_delta64_gradient_from_products_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_gradient_from_products_cv _ =
          SOME object_center_delta_gradient`
  >> drule_all
       (Q.INST
         [`word_environment` |-> `word_outer_environment`,
          `object_environment` |-> `object_outer_environment`,
          `word_result` |-> `word_box_delta_hessian`]
         compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_delta64_hessian_covers_object_q)
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_hessian_cv object_outer_environment =
          SOME object_box_delta_hessian`
  >> drule_all
       compute_boundedAnalyticObjectDeltaFourCoordinateRefinementTheory.bounded_delta64_four_coordinate_covers_object_q
  >> strip_tac
  >> `bounded_object_q_delta_four_coordinate_cv semantic_radii
        object_center_environment object_outer_environment coordinate =
      SOME
        (bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_product_center_value_cv
            object_center_environment coordinate)
          (bounded_case16594_object_delta_product_center_gradient_cv
            object_center_environment coordinate)
          (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
            semantic_radii object_center_environment
            object_outer_environment coordinate))` by
       (irule
          compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_semantic_environment
        >> simp [])
  >> gvs []
  >> `EVERY bounded_packed_q_interval_valid_cv object_center_environment /\
      EVERY bounded_packed_q_interval_valid_cv object_outer_environment` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `EVERY bounded_packed_q_interval_valid_cv object_center_delta_gradient /\
      EVERY bounded_packed_q_interval_valid_cv object_box_delta_hessian` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `object_center_delta_gradient =
        bounded_case16594_object_delta_product_center_delta_gradient_cv
          object_center_environment` by
       (Cases_on `object_center_environment` >> fs []
        >> Cases_on `t` >> fs []
        >> Cases_on `t'` >> fs []
        >> Cases_on `t` >> fs []
        >> Cases_on `t'` >> fs []
        >> Cases_on `t` >> fs []
        >> Cases_on `t'` >> fs []
        >> gvs
             [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_pair_products_cv_def,
              compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_semantic,
              compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def])
  >> `object_box_delta_hessian =
        bounded_object_q_delta_hessian_six_cv
          (EL 0 object_outer_environment) (EL 1 object_outer_environment)
          (EL 2 object_outer_environment) (EL 3 object_outer_environment)
          (EL 4 object_outer_environment) (EL 5 object_outer_environment)` by
       (Cases_on `object_outer_environment` >> fs []
        >> Cases_on `t` >> fs []
        >> Cases_on `t'` >> fs []
        >> Cases_on `t` >> fs []
        >> Cases_on `t'` >> fs []
        >> Cases_on `t` >> fs []
        >> Cases_on `t'` >> fs
             [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_hessian_cv_def])
  >> gvs []
  >> simp
       [compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_product_refinement_context_def,
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length,
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> `bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_product_center_value_cv
          object_center_environment coordinate) /\
      EVERY bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_product_center_gradient_cv
          object_center_environment coordinate) /\
      EVERY bounded_packed_q_interval_valid_cv
        (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
          semantic_radii object_center_environment object_outer_environment
          coordinate)` by
       (Cases_on `word_result`
        >> fs
             [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def,
              compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
              compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
        >> metis_tac
             [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_covers_packed_q_interval_valid_cv,
              compute_boundedPackedObjectSourceContractRefinementTheory.bounded_interval64_list_covers_packed_q_interval_valid_cv])
  >> simp
       [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_gradient_cv_def,
        compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_semantic_outer_hessian_cv_def,
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_hessian_length,
        compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def]
  >> `LENGTH
        (bounded_case16594_object_delta_product_hessian_cv coordinate
          (EL coordinate object_outer_environment)
          (bounded_object_q_taylor_gradient_complete_cv semantic_radii
            (bounded_case16594_object_delta_product_center_delta_gradient_cv
              object_center_environment)
            (bounded_object_q_delta_hessian_six_cv
              (EL 0 object_outer_environment) (EL 1 object_outer_environment)
              (EL 2 object_outer_environment) (EL 3 object_outer_environment)
              (EL 4 object_outer_environment) (EL 5 object_outer_environment)))
          bounded_case16594_object_delta_product_indices6
          (bounded_object_q_delta_hessian_six_cv
            (EL 0 object_outer_environment) (EL 1 object_outer_environment)
            (EL 2 object_outer_environment) (EL 3 object_outer_environment)
            (EL 4 object_outer_environment) (EL 5 object_outer_environment))) =
      LENGTH bounded_case16594_object_delta_product_indices6` by
       (irule
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_hessian_length
        >> simp
             [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def,
              compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length])
  >> gvs
       [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
        compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def]
QED

Theorem bounded_case16594_object_joint_neg3_runtime_step:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights semantic_center_boxes 3 /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes (BoundedAnalytic64NegDeltaDerivative 3) word_state =
      SOME word_next /\
  bounded_case16594_word_dispatch_packet_contracts
    (SND word_state) packet_rest /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes
      (EL 34 bounded_case16594_program)
      (BoundedAnalytic64NegDeltaDerivative 3)
      semantic_state semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 4) bounded_case16594_object_source34_cv
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
         bounded_case16594_object_neg3_dispatch_runtime_radii_refines)
  >> impl_tac >- fs []
  >> disch_then
       (qx_choose_then `runtime_result`
         (qx_choose_then `object_result` strip_assume_tac))
  >> mp_tac
       (Q.INST
         [`source` |-> `EL 34 bounded_case16594_program`,
          `coordinate` |-> `3`,
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
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source34_specialization_ok,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_neg_refinement_context_def]
  >> disch_then (qx_choose_then `object_next` strip_assume_tac)
  >> fs
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source34_specialization_ok]
  >> `bounded_case16594_object_dispatch_step_eval_above 524405
        (bounded_object_q_cv_list semantic_center_boxes)
        (bounded_object_q_cv_list semantic_outer_boxes)
        (bounded_object_q_cv_list runtime_radii)
        (Num 4) bounded_case16594_object_source34_cv
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

Theorem bounded_case16594_object_joint_product0_runtime_step:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights semantic_center_boxes semantic_outer_boxes 0 /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic64_state_covers_object_q word_state semantic_state /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes (BoundedAnalytic64FourCoordinateDelta 0) word_state =
      SOME word_next /\
  bounded_case16594_word_dispatch_packet_contracts
    (SND word_state) packet_rest /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (FST semantic_state)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes
      (EL 35 bounded_case16594_program)
      (BoundedAnalytic64FourCoordinateDelta 0)
      semantic_state semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 1) bounded_case16594_object_source35_cv
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
         bounded_case16594_object_product0_dispatch_runtime_radii_refines)
  >> impl_tac >- fs []
  >> disch_then
       (qx_choose_then `runtime_result`
         (qx_choose_then `object_result` strip_assume_tac))
  >> mp_tac
       (Q.INST
         [`source` |-> `EL 35 bounded_case16594_program`,
          `coordinate` |-> `0`,
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
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source35_specialization_ok,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_product_refinement_context_def]
  >> disch_then (qx_choose_then `object_next` strip_assume_tac)
  >> fs
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_source35_specialization_ok]
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
