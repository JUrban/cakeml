(*****************************************************************************
 * Zero-derivative shape of the genuine source-7 reciprocal.
 *
 * Source 6 is constant.  The inverse unary constructor therefore preserves
 * zero center-gradient and Hessian fields, and recompletion leaves its value
 * enclosure representation-equivalent to its center.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSource7SemanticShape
Ancestors
  compute_boundedCase16594ObjectSource6SemanticShape
  compute_boundedCase16594ObjectInverseStepSemanticEval
  compute_boundedCase16594ObjectUnaryZeroAlgebra
  compute_boundedObjectTaylorZeroAlgebra
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source6_gradient_bounds_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source6_result)
Proof
  `bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source6_result =
    bounded_object_q_taylor_gradient_complete_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source6_result)
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source6_result)` by
       (Cases_on `bounded_case16594_object_source5_result`
        >> simp
             [compute_boundedCase16594ObjectSqrtStepSemanticEvalTheory.bounded_case16594_object_source6_result_def,
              compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_sqrt_def,
              compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
              compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
              compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
              compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
              LET_THM])
  >> pop_assum SUBST1_TAC
  >> irule bounded_object_q_taylor_gradient_complete_decodes_zero
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
        compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_zero_lengths,
        compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_center_gradient_decodes_zero,
        compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_hessian_decodes_zero]
QED

Theorem bounded_case16594_object_source6_gradient_bounds_length:
  LENGTH
    (bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source6_result) = 6
Proof
  mp_tac
    compute_boundedCase16594ObjectSqrtStepSemanticEvalTheory.bounded_case16594_object_source6_semantic_valid
  >> Cases_on `bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def]
QED

Theorem bounded_case16594_object_source7_center_gradient_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source7_result)
Proof
  Cases_on `bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_result_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_inverse_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        LET_THM]
  >> irule bounded_object_q_interval_list_scale_decodes_zero
  >> conj_tac
  >- metis_tac
       [compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_inverse_certificate_outputs_valid,
        compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded,
        compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul]
  >> mp_tac
       compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_center_gradient_decodes_zero
  >> asm_rewrite_tac []
  >> simp
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def]
QED

Theorem bounded_case16594_object_source7_hessian_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source7_result)
Proof
  Cases_on `bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_result_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_inverse_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
        LET_THM]
  >> irule bounded_object_q_taylor_unary_hessian_decodes_zero
  >> mp_tac
       compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_inverse_certificate_outputs_valid
  >> mp_tac bounded_case16594_object_source6_gradient_bounds_decodes_zero
  >> mp_tac bounded_case16594_object_source6_gradient_bounds_length
  >> mp_tac
       compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_zero_lengths
  >> mp_tac
       compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_hessian_decodes_zero
  >> asm_rewrite_tac []
  >> simp
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded,
        compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add]
QED

Theorem bounded_case16594_object_source7_zero_lengths:
  LENGTH
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source7_result) = 6 /\
  LENGTH
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source7_result) = 21
Proof
  mp_tac
    compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_semantic_valid
  >> Cases_on `bounded_case16594_object_source7_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def]
QED

Theorem bounded_case16594_object_source7_value_bound_identity:
  bounded_object_q_taylor_value_bound
      bounded_case16594_object_source7_result =
    bounded_object_q_taylor_value_complete_cv
      (bounded_object_q_taylor_center
        bounded_case16594_object_source7_result)
      (bounded_object_q_taylor_error_cv
        bounded_case16594_object_cell0_word_radii
        (bounded_object_q_taylor_center_gradient
          bounded_case16594_object_source7_result)
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_hessian
          bounded_case16594_object_source7_result))
Proof
  Cases_on `bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_result_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_inverse_def,
        compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
        LET_THM]
QED

Theorem bounded_case16594_object_source7_error_decodes_zero:
  bounded_object_q_decodes_zero
    (bounded_object_q_taylor_error_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source7_result)
      bounded_case16594_object_cell0_weights
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source7_result))
Proof
  irule bounded_object_q_taylor_error_decodes_zero
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
        compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_weights_def,
        compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def,
        bounded_case16594_object_source7_zero_lengths,
        bounded_case16594_object_source7_center_gradient_decodes_zero,
        bounded_case16594_object_source7_hessian_decodes_zero]
QED

Theorem bounded_case16594_object_source7_value_bound_center_equiv:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source7_result)
    (bounded_object_q_taylor_center
      bounded_case16594_object_source7_result)
Proof
  rewrite_tac [bounded_case16594_object_source7_value_bound_identity]
  >> irule bounded_object_q_taylor_value_complete_zero_equiv
  >> simp
       [bounded_case16594_object_source7_error_decodes_zero]
  >> mp_tac
       compute_boundedCase16594ObjectInverseStepSemanticEvalTheory.bounded_case16594_object_source7_semantic_valid
  >> Cases_on `bounded_case16594_object_source7_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

val _ = export_theory ();
