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

Theorem bounded_object_q_neg_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_neg_cv left)
    (bounded_object_q_neg_cv right)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedQFoldRelationTheory.bounded_object_q_cv_equiv_decodes
  >> `bounded_object_q_ints (bounded_object_q_neg_cv left) =
        SOME (-left_numerator,left_denominator)` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes]
  >> `bounded_object_q_ints (bounded_object_q_neg_cv right) =
        SOME (-right_numerator,right_denominator)` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes]
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        integerTheory.INT_MUL_LNEG]
QED

Theorem bounded_object_q_interval_neg_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv left right ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_neg_cv left)
    (bounded_object_q_interval_neg_cv right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
    [bounded_object_q_interval_cv_equiv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_def]
  >> metis_tac [bounded_object_q_neg_cv_equiv_cong]
QED

Theorem bounded_object_q_interval_list_neg_rel:
  !left right.
    LIST_REL bounded_object_q_interval_cv_equiv left right ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (MAP bounded_object_q_interval_neg_cv left)
      (MAP bounded_object_q_interval_neg_cv right)
Proof
  Induct
  >> Cases_on `right`
  >> simp [LIST_REL_def,bounded_object_q_interval_neg_cv_equiv_cong]
QED

Theorem bounded_object_q_interval_list_cv_equiv_right_encoded:
  !runtime semantic.
    bounded_object_q_interval_list_cv_equiv runtime
      (bounded_object_q_cv_list semantic) ==>
    ?runtime_values.
      runtime = bounded_object_q_cv_list runtime_values /\
      LIST_REL bounded_object_q_interval_cv_equiv
        runtime_values semantic
Proof
  Induct_on `semantic`
  >> Cases_on `runtime`
  >> simp
    [bounded_object_q_interval_list_cv_equiv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     LIST_REL_def]
  >- (Cases_on `n`
      >> simp [bounded_object_q_interval_list_cv_equiv_def])
  >> gen_tac
  >> strip_tac
  >> first_x_assum (qspec_then `c0` mp_tac)
  >> impl_tac
  >- fs []
  >> strip_tac
  >> qexists_tac `c::runtime_values`
  >> simp
    [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     LIST_REL_def]
  >> fs []
QED

Theorem bounded_object_q_interval_list_neg_cv_equiv:
  bounded_object_q_interval_list_cv_equiv runtime
      (bounded_object_q_cv_list semantic) ==>
  ?runtime_values.
    runtime = bounded_object_q_cv_list runtime_values /\
    bounded_object_q_interval_list_cv_equiv
      (bounded_object_q_cv_list
        (MAP bounded_object_q_interval_neg_cv runtime_values))
      (bounded_object_q_cv_list
        (MAP bounded_object_q_interval_neg_cv semantic))
Proof
  strip_tac
  >> drule bounded_object_q_interval_list_cv_equiv_right_encoded
  >> strip_tac
  >> qexists_tac `runtime_values`
  >> simp [bounded_object_q_interval_list_cv_equiv_encoded]
  >> metis_tac [bounded_object_q_interval_list_neg_rel]
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
