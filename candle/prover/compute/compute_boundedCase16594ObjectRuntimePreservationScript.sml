(*****************************************************************************
 * Reusable runtime/semantic preservation lemmas for the genuine case-16594
 * object evaluator.
 *
 * Start with representation reflexivity and polynomial constants.  Later
 * packets extend the same relation across negation, addition, multiplication,
 * and the certified unary instructions.
 *****************************************************************************)
open compute_boundedObjectTaylorEquivalenceTheory
open compute_boundedObjectTaylorZeroAlgebraTheory
open compute_boundedCase16594ObjectPolyStepControlEvalTheory
open preamble

Theory compute_boundedCase16594ObjectRuntimePreservation
Ancestors
  compute_boundedObjectTaylorEquivalence
  compute_boundedObjectTaylorZeroAlgebra
  compute_boundedCase16594ObjectPolyStepControlEval
Libs
  bossLib preamble

Theorem bounded_object_q_interval_cv_equiv_refl:
  bounded_object_q_interval_encoded value ==>
  bounded_object_q_interval_cv_equiv value value
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> Cases_on `value`
  >> fs
    [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> simp [bounded_object_q_interval_cv_equiv_def]
  >> metis_tac
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl]
QED

Theorem bounded_object_q_interval_list_rel_refl:
  !values.
    EVERY bounded_object_q_interval_encoded values ==>
    LIST_REL bounded_object_q_interval_cv_equiv values values
Proof
  Induct
  >> simp [LIST_REL_def,bounded_object_q_interval_cv_equiv_refl]
QED

Theorem bounded_case16594_object_cv_list_identity:
  !values.
    bounded_case16594_object_cv_list values =
    bounded_object_q_cv_list values
Proof
  Induct
  >> simp
    [bounded_case16594_object_cv_list_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_object_zero_interval_identity:
  bounded_case16594_object_zero_interval_cv =
    bounded_analytic_source_q_interval_cv 0 0 0
Proof
  simp
    [bounded_case16594_object_zero_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def]
QED

Theorem bounded_case16594_object_constant_runtime_semantic_equiv:
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_constant_state_cv
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  rewrite_tac
    [bounded_case16594_object_constant_state_cv_def,
     bounded_case16594_object_zero_gradient6_cv_def,
     bounded_case16594_object_zero_hessian21_cv_def,
     bounded_case16594_object_cv_list_identity,
     bounded_case16594_object_zero_interval_identity,
     compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def]
  >> rewrite_tac [bounded_object_q_taylor_runtime_equiv_selectors]
  >> simp
    [bounded_object_q_taylor_domain_def,
     bounded_object_q_taylor_center_def,
     bounded_object_q_taylor_center_gradient_def,
     bounded_object_q_taylor_value_bound_def,
     bounded_object_q_taylor_gradient_bounds_def,
     bounded_object_q_taylor_hessian_def,
     bounded_object_q_interval_list_cv_equiv_encoded]
  >> simp
    [bounded_object_q_interval_cv_equiv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     LIST_REL_REPLICATE_same]
QED

val _ = export_theory ();
