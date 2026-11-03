(*****************************************************************************
 * Canonical semantic shape for the derivative fields of the first genuine
 * case-16594 object polynomial.
 *
 * Keep these closed semantic calculations independent of the multi-million
 * node production result.  The final bridge can then compose them with the
 * separately authenticated runtime fields without replaying either side.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolySemanticTheory
open compute_boundedObjectTaylorEquivalenceTheory
open compute_boundedObjectTaylorZeroAlgebraTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolySemanticShape
Ancestors
  compute_boundedCase16594ObjectFirstPolySemantic
  compute_boundedObjectTaylorEquivalence
  compute_boundedObjectTaylorZeroAlgebra
Libs
  bossLib preamble

Theorem bounded_case16594_object_source0_center_gradient_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source0_result)
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM]
  >> irule bounded_object_q_interval_fused_scale_add_decodes_zero
  >> simp
    [bounded_object_q_interval_neg_decodes_zero,
     bounded_object_q_interval_neg_cv_encoded]
QED

Theorem bounded_case16594_object_source0_center_gradient_length:
  LENGTH
    (bounded_object_q_taylor_center_gradient
      bounded_case16594_object_source0_result) = 6
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM]
  >> irule bounded_object_q_interval_fused_scale_add_cv_length6
  >> simp []
QED

Theorem bounded_case16594_object_source0_hessian_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source0_result)
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM]
  >> irule bounded_object_q_interval_fused_hessian_decodes_zero
  >> simp [bounded_object_q_interval_neg_decodes_zero]
  >> conj_tac
  >- (irule bounded_object_q_taylor_value_complete_cv_encoded
      >> simp [bounded_object_q_interval_neg_cv_encoded]
      >> irule bounded_object_q_taylor_error_cv_encoded
      >> simp
        [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
         compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_weights_def,
         compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def,
         bounded_object_q_interval_neg_cv_encoded])
  >> irule bounded_object_q_symmetric_product_pairs_decodes_zero
  >> simp []
  >> irule bounded_object_q_taylor_gradient_complete_cv_encoded
  >> simp
    [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
     bounded_object_q_interval_neg_cv_encoded]
QED

Theorem bounded_case16594_object_source0_hessian_length:
  LENGTH
    (bounded_object_q_taylor_hessian
      bounded_case16594_object_source0_result) = 21
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM]
  >> irule bounded_object_q_interval_fused_hessian_cv_length21
  >> simp []
  >> irule bounded_object_q_symmetric_product_pairs_cv_length6
  >> simp []
  >> irule bounded_object_q_taylor_gradient_complete_cv_length6
  >> simp []
QED

Theorem bounded_case16594_object_source0_gradient_bounds_decodes_zero:
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source0_result)
Proof
  `bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source0_result =
    bounded_object_q_taylor_gradient_complete_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source0_result)
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source0_result)` by
       simp
         [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
          compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
          LET_THM]
  >> pop_assum SUBST1_TAC
  >> irule bounded_object_q_taylor_gradient_complete_decodes_zero
  >> simp
    [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
     bounded_case16594_object_source0_center_gradient_length,
     bounded_case16594_object_source0_hessian_length,
     bounded_case16594_object_source0_center_gradient_decodes_zero,
     bounded_case16594_object_source0_hessian_decodes_zero]
QED

Theorem bounded_case16594_object_source0_gradient_bounds_length:
  LENGTH
    (bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source0_result) = 6
Proof
  `bounded_object_q_taylor_gradient_bounds
      bounded_case16594_object_source0_result =
    bounded_object_q_taylor_gradient_complete_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source0_result)
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source0_result)` by
       simp
         [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_gradient_bounds_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
          compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
          LET_THM]
  >> pop_assum SUBST1_TAC
  >> irule bounded_object_q_taylor_gradient_complete_cv_length6
  >> simp
    [bounded_case16594_object_source0_center_gradient_length,
     bounded_case16594_object_source0_hessian_length]
QED

Theorem bounded_case16594_object_source0_center_encoded:
  bounded_object_q_interval_encoded
    (bounded_object_q_taylor_center
      bounded_case16594_object_source0_result)
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM]
  >> irule bounded_object_q_interval_mul_cv_encoded
  >> simp [bounded_object_q_interval_neg_cv_encoded]
QED

Theorem bounded_case16594_object_source0_error_decodes_zero:
  bounded_object_q_decodes_zero
    (bounded_object_q_taylor_error_cv
      bounded_case16594_object_cell0_word_radii
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source0_result)
      bounded_case16594_object_cell0_weights
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source0_result))
Proof
  irule bounded_object_q_taylor_error_decodes_zero
  >> simp
    [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_weights_def,
     compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def,
     bounded_case16594_object_source0_center_gradient_length,
     bounded_case16594_object_source0_hessian_length,
     bounded_case16594_object_source0_center_gradient_decodes_zero,
     bounded_case16594_object_source0_hessian_decodes_zero]
QED

Theorem bounded_case16594_object_source0_value_bound_center_equiv:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source0_result)
    (bounded_object_q_taylor_center
      bounded_case16594_object_source0_result)
Proof
  `bounded_object_q_taylor_value_bound
      bounded_case16594_object_source0_result =
    bounded_object_q_taylor_value_complete_cv
      (bounded_object_q_taylor_center
        bounded_case16594_object_source0_result)
      (bounded_object_q_taylor_error_cv
        bounded_case16594_object_cell0_word_radii
        (bounded_object_q_taylor_center_gradient
          bounded_case16594_object_source0_result)
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_hessian
          bounded_case16594_object_source0_result))` by
       simp
         [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_hessian_def,
          compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
          LET_THM]
  >> pop_assum SUBST1_TAC
  >> irule bounded_object_q_taylor_value_complete_zero_equiv
  >> simp
    [bounded_case16594_object_source0_center_encoded,
     bounded_case16594_object_source0_error_decodes_zero]
QED

Theorem bounded_case16594_object_source0_gradient_bounds_zero_equiv:
  bounded_object_q_interval_list_cv_equiv
    (bounded_object_q_cv_list
      (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0)))
    (bounded_object_q_cv_list
      (bounded_object_q_taylor_gradient_bounds
        bounded_case16594_object_source0_result))
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded]
  >> rewrite_tac
       [GSYM bounded_case16594_object_source0_gradient_bounds_length]
  >> irule bounded_object_q_interval_zero_list_rel
  >> ACCEPT_TAC
       bounded_case16594_object_source0_gradient_bounds_decodes_zero
QED

Theorem bounded_case16594_object_source0_hessian_zero_equiv:
  bounded_object_q_interval_list_cv_equiv
    (bounded_object_q_cv_list
      (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0)))
    (bounded_object_q_cv_list
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source0_result))
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded]
  >> rewrite_tac [GSYM bounded_case16594_object_source0_hessian_length]
  >> irule bounded_object_q_interval_zero_list_rel
  >> ACCEPT_TAC bounded_case16594_object_source0_hessian_decodes_zero
QED

val _ = export_theory ();
