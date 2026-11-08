(*****************************************************************************
 * Compact semantic shape of the genuine source-5 polynomial.
 *
 * This polynomial is 1 - (1/3)^2.  Its derivative fields are all exact zero,
 * so its recomputed value enclosure is representation-equivalent to its
 * center.  Keeping these facts separate prevents the genuine sqrt
 * certificate proofs from reducing the complete polynomial evaluator.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSource5SemanticShape
Ancestors
  compute_boundedCase16594ObjectPrefixPolynomialInvariant
  compute_boundedObjectTaylorZeroAlgebra
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source5_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    bounded_case16594_object_source5_result
Proof
  simp [bounded_case16594_object_source5_result_def]
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_add_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
        compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_constant_semantic_valid]
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_neg_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs]
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_mul_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
        compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_constant_semantic_valid]
QED

Theorem bounded_case16594_object_source5_center_identity:
  bounded_object_q_taylor_center bounded_case16594_object_source5_result =
    bounded_object_q_interval_add_cv
      (bounded_analytic_source_q_interval_cv 1 0 0)
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          (bounded_analytic_source_q_interval_cv 1 0 2)
          (bounded_analytic_source_q_interval_cv 1 0 2)))
Proof
  simp
    [bounded_case16594_object_source5_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     LET_THM]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
        LET_THM]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        LET_THM]
QED

Theorem bounded_case16594_object_source5_center_gradient_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source5_result)
Proof
  simp
    [bounded_case16594_object_source5_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        LET_THM]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
        LET_THM]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        LET_THM,
        bounded_object_q_interval_neg_decodes_zero]
  >> EVAL_TAC
  >> simp []
QED

Theorem bounded_case16594_object_source5_hessian_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source5_result)
Proof
  simp
    [bounded_case16594_object_source5_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        LET_THM]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
        LET_THM]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
        LET_THM,
        bounded_object_q_interval_neg_decodes_zero]
  >> EVAL_TAC
  >> simp []
QED

Theorem bounded_case16594_object_source5_shape:
  bounded_object_q_interval_encoded
    (bounded_object_q_taylor_center
      bounded_case16594_object_source5_result) /\
  LENGTH
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source5_result) = 6 /\
  LENGTH
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source5_result) = 21
Proof
  mp_tac bounded_case16594_object_source5_semantic_valid
  >> Cases_on `bounded_case16594_object_source5_result`
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def]
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_source5_error_decodes_zero:
  bounded_object_q_decodes_zero
    (bounded_object_q_taylor_error_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source5_result)
      bounded_case16594_object_cell0_weights
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source5_result))
Proof
  irule bounded_object_q_taylor_error_decodes_zero
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
        compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_weights_def,
        compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def,
        bounded_case16594_object_source5_shape,
        bounded_case16594_object_source5_center_gradient_decodes_zero,
        bounded_case16594_object_source5_hessian_decodes_zero]
QED

Theorem bounded_case16594_object_source5_value_bound_identity:
  bounded_object_q_taylor_value_bound
      bounded_case16594_object_source5_result =
    bounded_object_q_taylor_value_complete_cv
      (bounded_object_q_taylor_center
        bounded_case16594_object_source5_result)
      (bounded_object_q_taylor_error_cv
        bounded_case16594_object_cell0_word_radii
        (bounded_object_q_taylor_center_gradient
          bounded_case16594_object_source5_result)
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_hessian
          bounded_case16594_object_source5_result))
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
     bounded_case16594_object_source5_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
     LET_THM]
QED

Theorem bounded_case16594_object_source5_value_bound_center_equiv:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source5_result)
    (bounded_object_q_taylor_center
      bounded_case16594_object_source5_result)
Proof
  rewrite_tac [bounded_case16594_object_source5_value_bound_identity]
  >> irule bounded_object_q_taylor_value_complete_zero_equiv
  >> simp
       [bounded_case16594_object_source5_shape,
        bounded_case16594_object_source5_error_decodes_zero]
QED

val _ = export_theory ();
