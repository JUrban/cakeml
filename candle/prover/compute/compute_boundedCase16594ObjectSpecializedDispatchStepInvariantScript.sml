(*****************************************************************************
 * Stack-level semantic adapters for the six authenticated specialized delta
 * branches in the genuine case-16594 dispatcher.
 *
 * The generic product/negative refinement bridges establish the numerical
 * result once.  This theory adds the exact source-position/code guard and
 * lifts the result through the complete runtime and semantic stacks.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSpecializedDispatchStepInvariant
Ancestors
  compute_boundedCase16594ObjectDeltaProductRefinementBridge
  compute_boundedCase16594ObjectDeltaNegRefinementBridge
  compute_boundedCase16594ObjectDispatchStepAboveEval
  compute_boundedCase16594ObjectPolyStackInvariant
  compute_boundedCase16594ProgramData
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_product_refinement_context_def:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes coordinate <=>
    coordinate < 6 /\
    EVERY bounded_packed_q_interval_valid_cv center_boxes /\
    LENGTH center_boxes = 6 /\
    EVERY bounded_packed_q_interval_valid_cv outer_boxes /\
    LENGTH outer_boxes = 6 /\
    bounded_taylor_radius_pairs semantic_radii = SOME weights /\
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_product_center_delta_gradient_cv
        center_boxes) /\
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_object_q_delta_hessian_six_cv
        (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
        (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) /\
    bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_product_center_value_cv
        center_boxes coordinate) /\
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_product_center_gradient_cv
        center_boxes coordinate) /\
    LENGTH
      (bounded_case16594_object_delta_product_center_gradient_cv
        center_boxes coordinate) = 6 /\
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
        semantic_radii center_boxes outer_boxes coordinate) /\
    LENGTH
      (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
        semantic_radii center_boxes outer_boxes coordinate) = 21
End

Definition bounded_case16594_object_delta_neg_refinement_context_def:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes coordinate <=>
    coordinate < 6 /\
    EVERY bounded_packed_q_interval_valid_cv center_boxes /\
    LENGTH center_boxes = 6 /\
    bounded_taylor_radius_pairs semantic_radii = SOME weights /\
    bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_neg_center_value_environment_cv
        center_boxes coordinate) /\
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_neg_center_gradient_environment_cv
        center_boxes coordinate) /\
    LENGTH
      (bounded_case16594_object_delta_neg_center_gradient_environment_cv
        center_boxes coordinate) = 6 /\
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) /\
    LENGTH
      (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate) = 21
End

Theorem bounded_case16594_object_delta_product_eval_above_runtime_refines:
  bounded_case16594_object_delta_product_refinement_context
    semantic_radii weights center_boxes outer_boxes coordinate ==>
  ?object_result.
    bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
      outer_boxes coordinate = SOME object_result /\
    bounded_case16594_object_expression_eval_above 524403
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_word64_object_q_cv semantic_radii));
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num coordinate)])
      (bounded_case16594_object_delta_product_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes outer_boxes coordinate) /\
    bounded_object_q_taylor_runtime_refines
      (bounded_case16594_object_delta_product_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes outer_boxes coordinate)
      object_result
Proof
  rw [bounded_case16594_object_delta_product_refinement_context_def]
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `outer_boxes` |-> `outer_boxes`,
          `coordinate` |-> `coordinate`]
         compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_source_state_semantic)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac `object_result`
  >> asm_rewrite_tac []
  >> conj_tac
  >- (rw
        [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_source_state_eval)
      >> simp
           [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded,
            listTheory.EVERY_MAP,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
      >> metis_tac
           [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths])
  >> rw
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def]
  >> `bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
        outer_boxes coordinate =
      SOME
        (bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_product_center_value_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_center_gradient_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
            semantic_radii center_boxes outer_boxes coordinate))` by
       (irule
          compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_semantic_environment
        >> simp [])
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def]
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_recomplete_semantic_valid
  >> simp []
  >> metis_tac
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
QED

Theorem bounded_case16594_object_delta_neg_eval_above_runtime_refines:
  bounded_case16594_object_delta_neg_refinement_context
    semantic_radii weights center_boxes coordinate ==>
  ?object_result.
    bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
      coordinate = SOME object_result /\
    bounded_case16594_object_expression_eval_above 262500
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_word64_object_q_cv semantic_radii));
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (Num coordinate)])
      (bounded_case16594_object_delta_neg_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes coordinate) /\
    bounded_object_q_taylor_runtime_refines
      (bounded_case16594_object_delta_neg_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes coordinate)
      object_result
Proof
  rw [bounded_case16594_object_delta_neg_refinement_context_def]
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `coordinate` |-> `coordinate`]
         compute_boundedCase16594ObjectDeltaNegRefinementBridgeTheory.bounded_case16594_object_delta_neg_source_state_semantic)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac `object_result`
  >> asm_rewrite_tac []
  >> conj_tac
  >- (rw
        [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_source_state_eval)
      >> simp
           [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded,
            listTheory.EVERY_MAP,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
      >> metis_tac
           [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths])
  >> rw
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def]
  >> `bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
        coordinate =
      SOME
        (bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_neg_center_value_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_center_gradient_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_hessian_six_list_cv
            coordinate))` by
       (irule
          compute_boundedCase16594ObjectDeltaNegRefinementBridgeTheory.bounded_case16594_object_delta_neg_semantic_environment
        >> simp [])
  >> gvs []
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def]
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_recomplete_semantic_valid
  >> simp []
  >> metis_tac
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
QED

Theorem bounded_case16594_object_source35_specialization_ok:
  bounded_analytic_specialization_ok (EL 35 bounded_case16594_program)
    (BoundedFourCoordinateDelta 0)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_product0_dispatch_stack_runtime_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes 0 /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv semantic_radii))
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
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `outer_boxes` |-> `outer_boxes`,
          `coordinate` |-> `0`]
         bounded_case16594_object_delta_product_eval_above_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_product_source_state_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          center_boxes outer_boxes 0`
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
        bounded_case16594_object_source35_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_source78_specialization_ok:
  bounded_analytic_specialization_ok (EL 78 bounded_case16594_program)
    (BoundedFourCoordinateDelta 1)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_product1_dispatch_stack_runtime_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes 1 /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv semantic_radii))
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
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `outer_boxes` |-> `outer_boxes`,
          `coordinate` |-> `1`]
         bounded_case16594_object_delta_product_eval_above_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_product_source_state_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          center_boxes outer_boxes 1`
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
        bounded_case16594_object_source78_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_source121_specialization_ok:
  bounded_analytic_specialization_ok (EL 121 bounded_case16594_program)
    (BoundedFourCoordinateDelta 2)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_product2_dispatch_stack_runtime_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes 2 /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv semantic_radii))
      (Num 3) bounded_case16594_object_source121_cv certificates
      (bounded_object_q_cv_list runtime_stack)
      (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
      certificates /\
    bounded_object_q_analytic_step semantic_radii weights center_boxes
      outer_boxes (EL 121 bounded_case16594_program)
      (BoundedAnalytic64FourCoordinateDelta 2)
      (semantic_stack,semantic_certificates)
      (object_result::semantic_stack,semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (object_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `outer_boxes` |-> `outer_boxes`,
          `coordinate` |-> `2`]
         bounded_case16594_object_delta_product_eval_above_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_product_source_state_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          center_boxes outer_boxes 2`
  >> qexists_tac `object_result`
  >> conj_tac
  >- (irule
        (SIMP_RULE arith_ss []
          (Q.INST [`numeric_floor` |-> `524403`]
            compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_product2_eval_above))
      >> fs [compute_execTheory.from_cv_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        bounded_case16594_object_source121_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_source34_specialization_ok:
  bounded_analytic_specialization_ok (EL 34 bounded_case16594_program)
    (BoundedNegDeltaDerivative 3)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_neg3_dispatch_stack_runtime_refines:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes 3 /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 262502
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv semantic_radii))
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
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `coordinate` |-> `3`]
         bounded_case16594_object_delta_neg_eval_above_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_neg_source_state_cv
          (MAP bounded_word64_object_q_cv semantic_radii) center_boxes 3`
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
        bounded_case16594_object_source34_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_source77_specialization_ok:
  bounded_analytic_specialization_ok (EL 77 bounded_case16594_program)
    (BoundedNegDeltaDerivative 4)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_neg4_dispatch_stack_runtime_refines:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes 4 /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 262502
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv semantic_radii))
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
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `coordinate` |-> `4`]
         bounded_case16594_object_delta_neg_eval_above_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_neg_source_state_cv
          (MAP bounded_word64_object_q_cv semantic_radii) center_boxes 4`
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
        bounded_case16594_object_source77_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_source120_specialization_ok:
  bounded_analytic_specialization_ok (EL 120 bounded_case16594_program)
    (BoundedNegDeltaDerivative 5)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_neg5_dispatch_stack_runtime_refines:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes 5 /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack ==>
  ?runtime_result object_result.
    bounded_case16594_object_dispatch_step_eval_above 262502
      (bounded_object_q_cv_list center_boxes)
      (bounded_object_q_cv_list outer_boxes)
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv semantic_radii))
      (Num 6) bounded_case16594_object_source120_cv certificates
      (bounded_object_q_cv_list runtime_stack)
      (Pair runtime_result (bounded_object_q_cv_list runtime_stack))
      certificates /\
    bounded_object_q_analytic_step semantic_radii weights center_boxes
      outer_boxes (EL 120 bounded_case16594_program)
      (BoundedAnalytic64NegDeltaDerivative 5)
      (semantic_stack,semantic_certificates)
      (object_result::semantic_stack,semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (object_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`, `coordinate` |-> `5`]
         bounded_case16594_object_delta_neg_eval_above_runtime_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac
       `bounded_case16594_object_delta_neg_source_state_cv
          (MAP bounded_word64_object_q_cv semantic_radii) center_boxes 5`
  >> qexists_tac `object_result`
  >> conj_tac
  >- (irule
        (SIMP_RULE arith_ss []
          (Q.INST [`numeric_floor` |-> `262500`]
            compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_neg5_eval_above))
      >> fs [compute_execTheory.from_cv_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
        bounded_case16594_object_source120_specialization_ok]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

val _ = export_theory ();
