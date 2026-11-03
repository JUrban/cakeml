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
open compute_boundedCase16594ObjectLinearEvalTheory
open compute_boundedPackedObjectPrimitiveAbsEvalTheory
open preamble

Theory compute_boundedCase16594ObjectRuntimePreservation
Ancestors
  compute_boundedObjectTaylorEquivalence
  compute_boundedObjectTaylorZeroAlgebra
  compute_boundedCase16594ObjectPolyStepControlEval
  compute_boundedCase16594ObjectLinearEval
  compute_boundedPackedObjectPrimitiveAbsEval
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

Theorem bounded_case16594_object_q_neg_encoded_eval:
  bounded_object_q_encoded value /\
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_neg» [from_cv value]) (refs:hol_refs) =
    (M_success (from_cv (bounded_object_q_neg_cv value)),refs)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs
    [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var ("positive",``:cv``) |-> ``Num positive``,
            mk_var ("negative",``:cv``) |-> ``Num negative``,
            mk_var ("denominator",``:cv``) |->
              ``Num denominator_minus_one``]
           bounded_case16594_object_q_neg_eval))
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_neg_encoded_eval:
  bounded_object_q_interval_encoded value /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg» [from_cv value]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_neg_cv value)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> gvs []
  >> fs [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs
    [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var ("lower_positive",``:cv``) |-> ``Num positive'``,
            mk_var ("lower_negative",``:cv``) |-> ``Num negative'``,
            mk_var ("lower_denominator",``:cv``) |->
              ``Num denominator_minus_one'``,
            mk_var ("upper_positive",``:cv``) |-> ``Num positive``,
            mk_var ("upper_negative",``:cv``) |-> ``Num negative``,
            mk_var ("upper_denominator",``:cv``) |->
              ``Num denominator_minus_one``]
           bounded_case16594_object_q_interval_neg_eval))
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_interval_list_neg_encoded_eval:
  !values clock refs.
    EVERY bounded_object_q_interval_encoded values /\
    LENGTH values + 2 < clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [from_cv (bounded_object_q_cv_list values)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (MAP bounded_object_q_interval_neg_cv values))),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> simp
        [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_object_interval_list_neg_nil_eval)
      >> intLib.ARITH_TAC)
  >> rpt strip_tac
  >> gvs []
  >> rw
    [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> gvs []
  >> fs [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> simp
    [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var ("lower_positive",``:cv``) |-> ``Num positive'``,
            mk_var ("lower_negative",``:cv``) |-> ``Num negative'``,
            mk_var ("lower_denominator",``:cv``) |->
              ``Num denominator_minus_one'``,
            mk_var ("upper_positive",``:cv``) |-> ``Num positive``,
            mk_var ("upper_negative",``:cv``) |-> ``Num negative``,
            mk_var ("upper_denominator",``:cv``) |->
              ``Num denominator_minus_one``]
           bounded_case16594_object_interval_list_neg_cons_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum irule
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
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

Theorem bounded_object_int_le_justify_multiplication:
  !multiplier left right:int.
    0 < multiplier ==>
    (left <= right <=> multiplier * left <= multiplier * right)
Proof
  rpt strip_tac
  >> mp_tac
       (Q.SPECL [`multiplier`,`right`,`left`]
         int_arithTheory.lt_justify_multiplication)
  >> metis_tac [integerTheory.INT_NOT_LT]
QED

Theorem bounded_object_q_le_cv_rep_equiv:
  bounded_object_q_ints left = SOME (left_numerator,left_denominator) /\
  bounded_object_q_ints left' = SOME (left_numerator',left_denominator') /\
  bounded_object_q_ints right = SOME (right_numerator,right_denominator) /\
  bounded_object_q_ints right' = SOME (right_numerator',right_denominator') /\
  left_numerator * left_denominator' =
    left_numerator' * left_denominator /\
  right_numerator * right_denominator' =
    right_numerator' * right_denominator ==>
  (bounded_object_q_le_cv left right =
   bounded_object_q_le_cv left' right')
Proof
  strip_tac
  >> `0 < left_denominator` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `0 < left_denominator'` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `0 < right_denominator` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `0 < right_denominator'` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `0 < left_denominator' * right_denominator'` by
       (irule
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> simp [])
  >> `0 < left_denominator * right_denominator` by
       (irule
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> simp [])
  >> `((left_numerator * right_denominator <=
          right_numerator * left_denominator) <=>
       (left_denominator' * right_denominator') *
          (left_numerator * right_denominator) <=
       (left_denominator' * right_denominator') *
          (right_numerator * left_denominator))` by
       metis_tac [bounded_object_int_le_justify_multiplication]
  >> `((left_numerator' * right_denominator' <=
          right_numerator' * left_denominator') <=>
       (left_denominator * right_denominator) *
          (left_numerator' * right_denominator') <=
       (left_denominator * right_denominator) *
          (right_numerator' * left_denominator'))` by
       metis_tac [bounded_object_int_le_justify_multiplication]
  >> `(left_denominator' * right_denominator') *
        (left_numerator * right_denominator) =
      (left_denominator * right_denominator) *
        (left_numerator' * right_denominator')` by
       metis_tac
         [integerTheory.INT_MUL_ASSOC,integerTheory.INT_MUL_COMM]
  >> `(left_denominator' * right_denominator') *
        (right_numerator * left_denominator) =
      (left_denominator * right_denominator) *
        (right_numerator' * left_denominator')` by
       metis_tac
         [integerTheory.INT_MUL_ASSOC,integerTheory.INT_MUL_COMM]
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
  >> fs
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_object_q_le_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left left' /\
  bounded_case10173_q_cv_equiv right right' ==>
  (bounded_object_q_le_cv left right =
   bounded_object_q_le_cv left' right')
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedQFoldRelationTheory.bounded_object_q_cv_equiv_decodes
  >> metis_tac [bounded_object_q_le_cv_rep_equiv]
QED

Theorem bounded_object_q_max_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left left' /\
  bounded_case10173_q_cv_equiv right right' ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_max_cv left right)
    (bounded_object_q_max_cv left' right')
Proof
  strip_tac
  >> `bounded_object_q_le_cv left right =
      bounded_object_q_le_cv left' right'` by
       metis_tac [bounded_object_q_le_cv_equiv_cong]
  >> rw
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_def]
  >> every_case_tac
  >> fs []
QED

Theorem bounded_object_q_abs_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_abs_cv left)
    (bounded_object_q_abs_cv right)
Proof
  strip_tac
  >> rw
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_abs_cv_def]
  >> irule bounded_object_q_max_cv_equiv_cong
  >> simp [bounded_object_q_neg_cv_equiv_cong]
QED

Theorem bounded_object_q_interval_abs_upper_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_interval_abs_upper_cv left)
    (bounded_object_q_interval_abs_upper_cv right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
    [bounded_object_q_interval_cv_equiv_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_interval_abs_upper_cv_def]
  >> strip_tac
  >> irule bounded_object_q_max_cv_equiv_cong
  >> simp [bounded_object_q_abs_cv_equiv_cong]
QED

Theorem bounded_packed_q_source_abs_upper_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_abs_upper_cv left)
    (bounded_packed_q_source_abs_upper_cv right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
    [bounded_object_q_interval_cv_equiv_def,
     compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_source_abs_upper_cv_def]
  >> metis_tac
    [bounded_object_q_max_cv_equiv_cong,
     bounded_object_q_neg_cv_equiv_cong]
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
