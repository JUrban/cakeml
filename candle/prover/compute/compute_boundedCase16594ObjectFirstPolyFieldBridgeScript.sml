(*****************************************************************************
 * Fieldwise semantic bridge for the first genuine object polynomial result.
 *
 * Keep each obligation independent so an expensive value-bound or completion
 * proof cannot hide the status of the center and derivative calculations.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolyResultFieldsTheory
open compute_boundedCase16594ObjectFirstPolySemanticTheory
open compute_boundedObjectTaylorEquivalenceTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolyFieldBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyResultFields
  compute_boundedCase16594ObjectFirstPolySemantic
  compute_boundedObjectTaylorEquivalence
Libs
  bossLib preamble

Theorem bounded_case16594_object_first_center_equiv:
  bounded_object_q_interval_cv_equiv
    bounded_case16594_object_first_result_center_cv
    (bounded_object_q_interval_mul_cv
      (bounded_analytic_source_q_interval_cv 1 0 0)
      (bounded_object_q_interval_neg_cv
        (bounded_analytic_source_q_interval_cv 13 0 499)))
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_center_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min4_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max4_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     LET_THM]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_first_domain_matches:
  bounded_case16594_object_first_result_domain_cv =
    (if bounded_object_q_taylor_domain
          bounded_case16594_object_source0_result
     then Num 1 else Num 0)
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_domain_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM]
QED

Theorem bounded_case16594_object_first_center_semantic_equiv:
  bounded_object_q_interval_cv_equiv
    bounded_case16594_object_first_result_center_cv
    (bounded_object_q_taylor_center
      bounded_case16594_object_source0_result)
Proof
  simp
    [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     LET_THM,
     bounded_case16594_object_first_center_equiv]
QED

Theorem bounded_case16594_object_first_center_gradient_semantic_equiv:
  bounded_object_q_interval_list_cv_equiv
    bounded_case16594_object_first_result_center_gradient_cv
    (bounded_object_q_cv_list
      (bounded_object_q_taylor_center_gradient
        bounded_case16594_object_source0_result))
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_center_gradient_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_gradient_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min4_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max4_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     LET_THM]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_first_hessian_zero_equiv:
  bounded_object_q_interval_list_cv_equiv
    bounded_case16594_object_first_result_hessian_cv
    (bounded_object_q_cv_list
      (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0)))
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_hessian_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_first_gradient_bounds_zero_equiv:
  bounded_object_q_interval_list_cv_equiv
    bounded_case16594_object_first_result_gradient_bounds_cv
    (bounded_object_q_cv_list
      (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0)))
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_gradient_bounds_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
