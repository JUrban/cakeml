(*****************************************************************************
 * Compact semantic facts for the genuine source-8 multiplication.
 *
 * This source is the constant 1/3 multiplied by the preceding reciprocal.
 * The first facts deliberately expose only its center and validity; later
 * zero-derivative facts can build on them without reducing the whole state.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSource8SemanticShape
Ancestors
  compute_boundedCase16594ObjectMulDispatchSemanticEval
  compute_boundedCase16594ObjectAtanCertificateRelations
  compute_boundedCase16594ObjectSource7SemanticShape
  compute_boundedObjectTaylorZeroAlgebra
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source7_center_identity:
  bounded_object_q_taylor_center bounded_case16594_object_source7_result =
    bounded_case16594_object_cell0_inverse_center_reciprocal_cv
Proof
  Cases_on `bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_result_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_inverse_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        LET_THM]
QED

Theorem bounded_case16594_object_source8_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    bounded_case16594_object_source8_result
Proof
  simp
    [compute_boundedCase16594ObjectMulDispatchSemanticEvalTheory.bounded_case16594_object_source8_result_def]
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_mul_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
        compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_constant_semantic_valid,
        compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_semantic_valid,
        compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source4_result_def]
QED

Theorem bounded_case16594_object_source8_center_identity:
  bounded_object_q_taylor_center bounded_case16594_object_source8_result =
    bounded_object_q_interval_mul_cv
      (bounded_analytic_source_q_interval_cv 1 0 2)
      bounded_case16594_object_cell0_inverse_center_reciprocal_cv
Proof
  Cases_on `bounded_case16594_object_source7_result`
  >> mp_tac bounded_case16594_object_source7_center_identity
  >> simp
       [compute_boundedCase16594ObjectMulDispatchSemanticEvalTheory.bounded_case16594_object_source8_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source4_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        LET_THM]
QED

Theorem bounded_case16594_object_source8_center_certificate_encloses:
  bounded_object_q_interval_encloses
    bounded_case16594_object_cell0_atan_center_input_cv
    (bounded_object_q_taylor_center bounded_case16594_object_source8_result)
Proof
  rewrite_tac [bounded_case16594_object_source8_center_identity]
  >> rewrite_tac
    [compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_input_cv_def,
     compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_interval_encloses_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source8_center_gradient_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source8_result)
Proof
  Cases_on `bounded_case16594_object_source7_result`
  >> simp
       [compute_boundedCase16594ObjectMulDispatchSemanticEvalTheory.bounded_case16594_object_source8_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source4_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        LET_THM]
  >> irule bounded_object_q_interval_fused_scale_add_decodes_zero
  >> mp_tac
       compute_boundedCase16594ObjectSource7SemanticShapeTheory.bounded_case16594_object_source7_center_gradient_decodes_zero
  >> mp_tac
       compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_semantic_valid
  >> asm_rewrite_tac []
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_source8_hessian_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source8_result)
Proof
  Cases_on `bounded_case16594_object_source7_result`
  >> simp
       [compute_boundedCase16594ObjectMulDispatchSemanticEvalTheory.bounded_case16594_object_source8_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        compute_boundedCase16594ObjectPrefixPolynomialInvariantTheory.bounded_case16594_object_source4_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
        LET_THM]
  >> irule bounded_object_q_interval_fused_hessian_decodes_zero
  >> mp_tac
       compute_boundedCase16594ObjectSource7SemanticShapeTheory.bounded_case16594_object_source7_hessian_decodes_zero
  >> mp_tac
       compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_semantic_valid
  >> asm_rewrite_tac []
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def]
  >> rpt disch_tac
  >> conj_tac
  >- metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
  >> irule bounded_object_q_symmetric_product_pairs_decodes_zero
  >> simp []
  >> irule
       compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_packed_q_interval_valid_cv_list_object_encoded
  >> simp []
QED

Theorem bounded_case16594_object_source8_zero_lengths:
  LENGTH
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source8_result) = 6 /\
  LENGTH
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source8_result) = 21
Proof
  mp_tac bounded_case16594_object_source8_semantic_valid
  >> Cases_on `bounded_case16594_object_source8_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def]
QED

Theorem bounded_case16594_object_source8_value_bound_identity:
  bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result =
    bounded_object_q_taylor_value_complete_cv
      (bounded_object_q_taylor_center
        bounded_case16594_object_source8_result)
      (bounded_object_q_taylor_error_cv
        bounded_case16594_object_cell0_word_radii
        (bounded_object_q_taylor_center_gradient
          bounded_case16594_object_source8_result)
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_hessian
          bounded_case16594_object_source8_result))
Proof
  Cases_on `bounded_case16594_object_source4_result`
  >> Cases_on `bounded_case16594_object_source7_result`
  >> simp
       [compute_boundedCase16594ObjectMulDispatchSemanticEvalTheory.bounded_case16594_object_source8_result_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
        LET_THM]
QED

Theorem bounded_case16594_object_source8_error_decodes_zero:
  bounded_object_q_decodes_zero
    (bounded_object_q_taylor_error_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source8_result)
      bounded_case16594_object_cell0_weights
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source8_result))
Proof
  irule bounded_object_q_taylor_error_decodes_zero
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
        compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_weights_def,
        compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def,
        bounded_case16594_object_source8_zero_lengths,
        bounded_case16594_object_source8_center_gradient_decodes_zero,
        bounded_case16594_object_source8_hessian_decodes_zero]
QED

Theorem bounded_case16594_object_source8_value_bound_center_equiv:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result)
    (bounded_object_q_taylor_center
      bounded_case16594_object_source8_result)
Proof
  rewrite_tac [bounded_case16594_object_source8_value_bound_identity]
  >> irule bounded_object_q_taylor_value_complete_zero_equiv
  >> simp [bounded_case16594_object_source8_error_decodes_zero]
  >> mp_tac bounded_case16594_object_source8_semantic_valid
  >> Cases_on `bounded_case16594_object_source8_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

val _ = export_theory ();
