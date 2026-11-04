(*****************************************************************************
 * Generic semantic refinement for production atan certificate packets.
 *
 * Unlike the earlier genuine-packet theorem, this layer contains no fixed
 * case-16594 certificate bytes or instruction index.  The evaluator guard
 * is generalized separately; this file establishes the reusable state
 * relation that its successful result must preserve.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant
Ancestors
  compute_boundedCase16594ObjectCertifiedSqrtDispatchInvariant
  compute_boundedCase16594ObjectAtanStepSemanticEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_atan_second_equiv_cong_generic:
  bounded_packed_q_interval_valid_cv derivative_square /\
  bounded_object_q_interval_cv_equiv runtime_source semantic_source ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_atan_second_cv runtime_source derivative_square)
    (bounded_object_q_atan_second_cv semantic_source derivative_square)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_second_cv_def]
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_neg_cv_equiv_cong
  >> irule
       compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_atan_decomposition_runtime_refines:
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv center_result /\
  bounded_packed_q_interval_valid_cv center_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative_square /\
  bounded_object_q_taylor_runtime_refines runtime_item semantic_state /\
  runtime_item =
    bounded_case16594_object_state_cv runtime_domain runtime_center
      (bounded_object_q_cv_list runtime_center_gradient)
      runtime_value_bound
      (bounded_object_q_cv_list runtime_gradient_bounds)
      (bounded_object_q_cv_list runtime_hessian) ==>
  runtime_domain =
    (if bounded_object_q_taylor_domain semantic_state
     then Num 1 else Num 0) /\
  bounded_object_q_taylor_runtime_refines
    (compute_boundedCase16594ObjectUnaryCompleteEval$bounded_case16594_object_state_unary_cv
      runtime_radii runtime_domain center_result center_derivative
      box_derivative
      (bounded_object_q_atan_second_cv runtime_value_bound
        box_derivative_square)
      runtime_center_gradient runtime_gradient_bounds runtime_hessian)
    (bounded_object_q_taylor_atan semantic_radii weights center_result
      center_derivative box_derivative box_derivative_square
      semantic_state)
Proof
  Cases_on `semantic_state`
  >> strip_tac
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_atan_second_cv c0 box_derivative_square)` by
       (irule
          compute_boundedCase16594ObjectAtanStepSemanticEvalTheory.bounded_case16594_object_atan_second_valid
        >> fs
             [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
              compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def])
  >> `bounded_object_q_interval_cv_equiv center_result center_result /\
      bounded_object_q_interval_cv_equiv
        center_derivative center_derivative /\
      bounded_object_q_interval_cv_equiv box_derivative box_derivative` by
       (rpt conj_tac
        >> irule
             compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
        >> metis_tac
             [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded])
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_encoded_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded]
  >> conj_tac
  >- (asm_simp_tac std_ss
        [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_atan_def]
      >> irule
           (REWRITE_RULE
             [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def]
             compute_boundedCase16594ObjectUnaryRelationTheory.bounded_case16594_object_unary_runtime_semantic_equiv)
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
      >> irule bounded_case16594_object_atan_second_equiv_cong_generic
      >> asm_rewrite_tac [])
  >> rewrite_tac
       [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_atan_def]
  >> irule
       compute_boundedCase16594ObjectUnaryRelationTheory.bounded_object_q_taylor_unary_semantic_valid
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
QED

val _ = export_theory ();
