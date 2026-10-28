(*****************************************************************************
 * Exact-rational bridge from the conservative analytic object bound to the
 * source-faithful five-payload entry contract.
 *****************************************************************************)
Theory compute_boundedPackedObjectSourceContractRefinement
Ancestors
  compute_boundedPackedObjectEntryRefinement
  compute_boundedCase16594OrdinaryAcceptBoundary
Libs
  bossLib preamble intLib

Definition bounded_int_fraction_rep_equiv_def:
  bounded_int_fraction_rep_equiv (left:int # int) (right:int # int) <=>
    FST left * SND right = FST right * SND left
End

Theorem bounded_int_fraction_neg_positive:
  bounded_int_fraction_positive fraction ==>
  bounded_int_fraction_positive (bounded_int_fraction_neg fraction)
Proof
  PairCases_on `fraction`
  >> simp
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_neg_def]
QED

Theorem bounded_int_fraction_right_le_max:
  bounded_int_fraction_positive left /\
  bounded_int_fraction_positive right ==>
  bounded_int_fraction_le right
    (bounded_int_fraction_max left right)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> rw
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_max_le:
  bounded_int_fraction_le left bound /\
  bounded_int_fraction_le right bound ==>
  bounded_int_fraction_le
    (bounded_int_fraction_max left right) bound
Proof
  rw
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_int_fraction_neg_le_reverse:
  bounded_int_fraction_le left right ==>
  bounded_int_fraction_le
    (bounded_int_fraction_neg right)
    (bounded_int_fraction_neg left)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> simp
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_neg_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_le_antisym_rep_equiv:
  bounded_int_fraction_le left right /\
  bounded_int_fraction_le right left ==>
  bounded_int_fraction_rep_equiv left right
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> simp
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def,
        bounded_int_fraction_rep_equiv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_source_abs_upper_valid:
  bounded_int_fraction_interval_valid (lower,upper) ==>
  bounded_int_fraction_rep_equiv
    (bounded_int_fraction_max (bounded_int_fraction_neg lower) upper)
    (bounded_int_fraction_interval_abs_upper (lower,upper))
Proof
  rw
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_interval_abs_upper_def]
  >> qabbrev_tac
       `lower_abs = bounded_int_fraction_abs lower`
  >> qabbrev_tac
       `upper_abs = bounded_int_fraction_abs upper`
  >> qabbrev_tac
       `source = bounded_int_fraction_max
          (bounded_int_fraction_neg lower) upper`
  >> qabbrev_tac
       `conservative = bounded_int_fraction_max lower_abs upper_abs`
  >> `bounded_int_fraction_positive (bounded_int_fraction_neg lower)` by
       metis_tac [bounded_int_fraction_neg_positive]
  >> `bounded_int_fraction_positive (bounded_int_fraction_neg upper)` by
       metis_tac [bounded_int_fraction_neg_positive]
  >> `bounded_int_fraction_positive lower_abs` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_positive,
              bounded_int_fraction_neg_positive])
  >> `bounded_int_fraction_positive upper_abs` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_positive,
              bounded_int_fraction_neg_positive])
  >> `bounded_int_fraction_positive source` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_positive,
              bounded_int_fraction_neg_positive])
  >> `bounded_int_fraction_positive conservative` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_positive,
              bounded_int_fraction_neg_positive])
  >> `bounded_int_fraction_le (bounded_int_fraction_neg lower) lower_abs` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
              bounded_int_fraction_right_le_max])
  >> `bounded_int_fraction_le lower_abs conservative` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_left_le_max])
  >> `bounded_int_fraction_le
        (bounded_int_fraction_neg lower) conservative` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_transitive]
  >> `bounded_int_fraction_le upper upper_abs` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
              compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_left_le_max])
  >> `bounded_int_fraction_le upper_abs conservative` by
       (unabbrev_all_tac
        >> simp [bounded_int_fraction_right_le_max])
  >> `bounded_int_fraction_le upper conservative` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_transitive]
  >> `bounded_int_fraction_le source conservative` by
       (unabbrev_all_tac
        >> metis_tac [bounded_int_fraction_max_le])
  >> `bounded_int_fraction_le upper source` by
       (unabbrev_all_tac
        >> simp [bounded_int_fraction_right_le_max])
  >> `bounded_int_fraction_le lower source` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_transitive]
  >> `bounded_int_fraction_le
        (bounded_int_fraction_neg lower) source` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_left_le_max])
  >> `bounded_int_fraction_le
        (bounded_int_fraction_neg upper)
        (bounded_int_fraction_neg lower)` by
       metis_tac [bounded_int_fraction_neg_le_reverse]
  >> `bounded_int_fraction_le
        (bounded_int_fraction_neg upper) source` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_transitive]
  >> `bounded_int_fraction_le lower_abs source` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
              bounded_int_fraction_max_le])
  >> `bounded_int_fraction_le upper_abs source` by
       (unabbrev_all_tac
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
              bounded_int_fraction_max_le])
  >> `bounded_int_fraction_le conservative source` by
       (unabbrev_all_tac
        >> metis_tac [bounded_int_fraction_max_le])
  >> unabbrev_all_tac
  >> metis_tac [bounded_int_fraction_le_antisym_rep_equiv]
QED

Theorem bounded_packed_q_source_abs_upper_decodes:
  bounded_object_q_interval_ints object_interval =
      SOME (lower,upper) ==>
  bounded_object_q_ints
      (bounded_packed_q_source_abs_upper_cv object_interval) =
    SOME
      (bounded_int_fraction_max
        (bounded_int_fraction_neg lower) upper)
Proof
  Cases_on `object_interval`
  >> rw
       [compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_q_source_abs_upper_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> `bounded_object_q_ints (bounded_object_q_neg_cv c) =
        SOME (bounded_int_fraction_neg lower)` by
       (PairCases_on `lower`
        >> simp
             [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_neg_def]
        >> irule
             compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes
        >> simp [])
  >> irule
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_decodes
  >> simp []
QED

Theorem bounded_packed_q_source_abs_upper_equiv:
  bounded_object_q_interval_ints object_interval = SOME decoded /\
  bounded_int_fraction_interval_valid decoded ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_abs_upper_cv object_interval)
    (bounded_object_q_interval_abs_upper_cv object_interval)
Proof
  Cases_on `decoded`
  >> rpt strip_tac
  >> `bounded_object_q_ints
        (bounded_packed_q_source_abs_upper_cv object_interval) =
      SOME
        (bounded_int_fraction_max
          (bounded_int_fraction_neg q) r)` by
       metis_tac [bounded_packed_q_source_abs_upper_decodes]
  >> `bounded_object_q_ints
        (bounded_object_q_interval_abs_upper_cv object_interval) =
      SOME
        (bounded_int_fraction_interval_abs_upper
          (q,r))` by
       metis_tac
         [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_interval_abs_upper_cv_decodes]
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> imp_res_tac bounded_int_fraction_source_abs_upper_valid
  >> Cases_on `bounded_int_fraction_max (bounded_int_fraction_neg q) r`
  >> Cases_on `bounded_int_fraction_interval_abs_upper (q,r)`
  >> gvs [bounded_int_fraction_rep_equiv_def]
QED

Definition bounded_packed_q_interval_valid_cv_def:
  bounded_packed_q_interval_valid_cv object_interval <=>
    ?decoded.
      bounded_object_q_interval_ints object_interval = SOME decoded /\
      bounded_int_fraction_interval_valid decoded
End

Theorem bounded_packed_q_interval_valid_cv_encoded:
  bounded_packed_q_interval_valid_cv object_interval ==>
  bounded_packed_q_interval_encoded object_interval
Proof
  strip_tac
  >> `bounded_object_q_interval_encoded object_interval` by
       fs
         [bounded_packed_q_interval_valid_cv_def,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> simp
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
QED

Theorem bounded_packed_q_interval_valid_cv_list_encoded:
  !object_intervals.
    EVERY bounded_packed_q_interval_valid_cv object_intervals ==>
    EVERY bounded_packed_q_interval_encoded object_intervals
Proof
  Induct
  >> simp [bounded_packed_q_interval_valid_cv_encoded]
QED

Theorem bounded_packed_q_valid_source_abs_upper_equiv:
  bounded_packed_q_interval_valid_cv object_interval ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_abs_upper_cv object_interval)
    (bounded_object_q_interval_abs_upper_cv object_interval)
Proof
  rw [bounded_packed_q_interval_valid_cv_def]
  >> metis_tac [bounded_packed_q_source_abs_upper_equiv]
QED

Theorem bounded_packed_q_source_dot_abs_upper_equiv:
  !radii entries.
    EVERY bounded_object_q_encoded radii /\
    EVERY bounded_packed_q_interval_valid_cv entries ==>
    bounded_case10173_q_cv_equiv
      (bounded_packed_q_source_dot_abs_upper_cv radii entries)
      (bounded_object_q_right_sum_cv
        (bounded_object_q_exact_dot_terms_cv radii entries))
Proof
  Induct_on `radii`
  >> Cases_on `entries`
  >> simp
       [compute_boundedPackedObjectDotEvalTheory.bounded_packed_q_source_dot_abs_upper_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_dot_terms_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_right_sum_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
  >> rpt strip_tac
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> conj_tac
  >- (irule
        compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
      >> conj_tac
      >- simp
           [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
      >> simp [bounded_packed_q_valid_source_abs_upper_equiv])
  >> metis_tac []
QED

Theorem bounded_packed_q_source_quadratic_term_equiv:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right /\
  bounded_packed_q_interval_valid_cv entry ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_quadratic_term_cv
      left right twice entry)
    (bounded_object_q_exact_quadratic_contribution_cv
      left right twice entry)
Proof
  strip_tac
  >> `bounded_object_q_encoded
        (bounded_object_q_mul_cv left right)` by
       simp
         [compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_quadratic_raw_cv left right entry)
        (bounded_object_q_mul_cv
          (bounded_object_q_mul_cv left right)
          (bounded_object_q_interval_abs_upper_cv entry))` by
       (rw
          [compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_q_source_quadratic_raw_cv_def]
        >> irule
             compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
        >> simp
             [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl,
              bounded_packed_q_valid_source_abs_upper_equiv])
  >> Cases_on `twice`
  >> simp
       [compute_boundedPackedObjectQuadraticTermEvalTheory.bounded_packed_q_source_quadratic_term_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_quadratic_contribution_cv_def,
        LET_THM]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong]
QED

Definition bounded_packed_q_source_exact_quadratic_terms_cv_def:
  bounded_packed_q_source_exact_quadratic_terms_cv [] [] = [] /\
  bounded_packed_q_source_exact_quadratic_terms_cv [] (_::_) = [] /\
  bounded_packed_q_source_exact_quadratic_terms_cv (_::_) [] = [] /\
  bounded_packed_q_source_exact_quadratic_terms_cv
      ((left,right,twice)::weights) (entry::entries) =
    bounded_packed_q_source_quadratic_term_cv
      left right twice entry ::
    bounded_packed_q_source_exact_quadratic_terms_cv weights entries
End

Theorem bounded_packed_q_source_exact_quadratic_terms_rel:
  !weights entries.
    EVERY
      (\(left,right,twice).
        bounded_object_q_encoded left /\
        bounded_object_q_encoded right) weights /\
    EVERY bounded_packed_q_interval_valid_cv entries ==>
    LIST_REL bounded_case10173_q_cv_equiv
      (bounded_packed_q_source_exact_quadratic_terms_cv weights entries)
      (bounded_object_q_exact_quadratic_terms_cv weights entries)
Proof
  Induct_on `weights`
  >- (Cases_on `entries`
      >> simp
           [bounded_packed_q_source_exact_quadratic_terms_cv_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_quadratic_terms_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
       [bounded_packed_q_source_exact_quadratic_terms_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_quadratic_terms_cv_def]
  >> metis_tac [bounded_packed_q_source_quadratic_term_equiv]
QED

Theorem bounded_packed_q_right_sum_rel_equiv:
  !left right.
    LIST_REL bounded_case10173_q_cv_equiv left right ==>
    bounded_case10173_q_cv_equiv
      (bounded_object_q_right_sum_cv left)
      (bounded_object_q_right_sum_cv right)
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> simp
       [LIST_REL_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_right_sum_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_zero_cv_encoded,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
  >> rpt strip_tac
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> metis_tac []
QED

Theorem bounded_packed_q_source_exact_quadratic_sum_equiv:
  EVERY
    (\(left,right,twice).
      bounded_object_q_encoded left /\
      bounded_object_q_encoded right) weights /\
  EVERY bounded_packed_q_interval_valid_cv entries ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_right_sum_cv
      (bounded_packed_q_source_exact_quadratic_terms_cv weights entries))
    (bounded_object_q_right_sum_cv
      (bounded_object_q_exact_quadratic_terms_cv weights entries))
Proof
  metis_tac
    [bounded_packed_q_source_exact_quadratic_terms_rel,
     bounded_packed_q_right_sum_rel_equiv]
QED

Theorem bounded_object_q_exact_radius_pairs6_encoded:
  bounded_object_q_exact_radius_pairs6_cv radii = SOME weights /\
  EVERY bounded_object_q_encoded radii ==>
  EVERY
    (\(left,right,twice).
      bounded_object_q_encoded left /\
      bounded_object_q_encoded right) weights
Proof
  rw
    [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_radius_pairs6_cv_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_packed_q_source_quadratic6_is_generic:
  bounded_object_q_exact_radius_pairs6_cv radii = SOME weights /\
  LENGTH entries = 21 ==>
  bounded_packed_q_source_quadratic_suffix6_cv
      0 (HD radii) (EL 1 radii) (EL 2 radii)
      (EL 3 radii) (EL 4 radii) (EL 5 radii) entries =
    bounded_object_q_right_sum_cv
      (bounded_packed_q_source_exact_quadratic_terms_cv weights entries)
Proof
  rw
    [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_radius_pairs6_cv_def]
  >> every_case_tac
  >> gvs
       [LENGTH_EQ_NUM_compute,
        compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_suffix6_cv_def,
        compute_boundedPackedObjectQuadraticEvalTheory.bounded_packed_q_source_quadratic_terms6_cv_def,
        bounded_packed_q_source_exact_quadratic_terms_cv_def,
        compute_boundedQFoldRelationTheory.bounded_object_q_right_sum_cv_def]
QED

Theorem bounded_packed_q_source_quadratic6_equiv:
  bounded_object_q_exact_radius_pairs6_cv radii = SOME weights /\
  EVERY bounded_object_q_encoded radii /\
  EVERY bounded_packed_q_interval_valid_cv entries /\
  LENGTH entries = 21 ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_quadratic_suffix6_cv
      0 (HD radii) (EL 1 radii) (EL 2 radii)
      (EL 3 radii) (EL 4 radii) (EL 5 radii) entries)
    (bounded_object_q_right_sum_cv
      (bounded_object_q_exact_quadratic_terms_cv weights entries))
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_exact_radius_pairs6_encoded
  >> imp_res_tac bounded_packed_q_source_quadratic6_is_generic
  >> asm_rewrite_tac []
  >> metis_tac [bounded_packed_q_source_exact_quadratic_sum_equiv]
QED

Theorem bounded_packed_q_source_error6_equiv:
  bounded_object_q_exact_radius_pairs6_cv radii = SOME weights /\
  EVERY bounded_object_q_encoded radii /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_error6_cv
      radii center_gradient hessian)
    (bounded_object_q_exact_packed_error6_cv
      radii center_gradient hessian)
Proof
  strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_dot_abs_upper_cv
          radii center_gradient)
        (bounded_object_q_right_sum_cv
          (bounded_object_q_exact_dot_terms_cv
            radii center_gradient))` by
       metis_tac [bounded_packed_q_source_dot_abs_upper_equiv]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_quadratic_suffix6_cv
          0 (HD radii) (EL 1 radii) (EL 2 radii)
          (EL 3 radii) (EL 4 radii) (EL 5 radii) hessian)
        (bounded_object_q_right_sum_cv
          (bounded_object_q_exact_quadratic_terms_cv
            weights hessian))` by
       metis_tac [bounded_packed_q_source_quadratic6_equiv]
  >> rw
       [compute_boundedPackedObjectErrorEvalTheory.bounded_packed_q_source_error6_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_packed_error6_cv_def,
        LET_THM]
  >> asm_rewrite_tac []
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> simp []
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> simp []
QED

Theorem bounded_packed_q_source_value_upper_equiv:
  bounded_object_q_exact_radius_pairs6_cv radii = SOME weights /\
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_valid_cv center_value /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_interval_upper_cv
      (bounded_packed_q_source_value_bound6_cv
        radii center_value center_gradient hessian))
    (bounded_object_q_exact_packed_value_upper6_cv
      radii center_value center_gradient hessian)
Proof
  strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_error6_cv
          radii center_gradient hessian)
        (bounded_object_q_exact_packed_error6_cv
          radii center_gradient hessian)` by
       metis_tac [bounded_packed_q_source_error6_equiv]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_half_error_cv
          radii center_gradient hessian)
        (bounded_object_q_ordinary_half_error_cv
          (bounded_object_q_exact_packed_error6_cv
            radii center_gradient hessian))` by
       (rw
          [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_half_error_cv_def,
           compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_ordinary_half_error_cv_def]
        >> irule
             compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
        >> simp
             [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded,
              compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl])
  >> imp_res_tac bounded_packed_q_interval_valid_cv_encoded
  >> fs
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> rw
       [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_value_bound6_cv_def,
        compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_cv_def,
        compute_boundedPackedObjectFinishEvalTheory.bounded_packed_q_source_interval_upper_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_packed_value_upper6_cv_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_ordinary_value_upper_cv_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_upper_cv_def,
        LET_THM]
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong
  >> simp
       [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
QED

Theorem bounded_object_q_exact_packed_accept_refines_source:
  bounded_object_q_exact_radius_pairs6_cv radii = SOME weights /\
  EVERY bounded_object_q_encoded radii /\
  bounded_packed_q_interval_valid_cv center_value /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  bounded_object_q_exact_packed_accept6 T radii center_value
    center_gradient hessian ==>
  bounded_packed_object_source_accept6 radii center_value
    center_gradient hessian
Proof
  strip_tac
  >> fs
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_packed_accept6_def]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv
            radii center_value center_gradient hessian))
        (bounded_object_q_exact_packed_value_upper6_cv
          radii center_value center_gradient hessian)` by
       metis_tac [bounded_packed_q_source_value_upper_equiv]
  >> `bounded_object_q_strict_negative_cv
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv
            radii center_value center_gradient hessian))` by
       metis_tac
         [compute_boundedQRelationAlgebraTheory.bounded_case10173_q_cv_equiv_sym,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_strict_negative_equiv]
  >> rw
       [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> simp
       [bounded_packed_q_interval_valid_cv_encoded,
        bounded_packed_q_interval_valid_cv_list_encoded]
QED

Theorem bounded_interval64_covers_packed_q_interval_valid_cv:
  bounded_interval64_covers_object_q word_interval object_interval ==>
  bounded_packed_q_interval_valid_cv object_interval
Proof
  rw
    [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
     bounded_packed_q_interval_valid_cv_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_interval64_covers_object_q_ints_valid]
QED

Theorem bounded_interval64_list_covers_packed_q_interval_valid_cv:
  !word_intervals object_intervals.
    LIST_REL bounded_interval64_covers_object_q
      word_intervals object_intervals ==>
    EVERY bounded_packed_q_interval_valid_cv object_intervals
Proof
  Induct
  >> Cases_on `object_intervals`
  >> simp [LIST_REL_def]
  >> metis_tac [bounded_interval64_covers_packed_q_interval_valid_cv]
QED

Theorem bounded_packed_object_ordinary_accept_refines_source:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_covers_object_q word_result
    (BoundedObjectQTaylor object_domain center_value center_gradient
      value_bound gradient_bounds hessian) /\
  bounded_object_q_ordinary_accept6 object_domain radii center_value
    center_gradient weights hessian ==>
  bounded_packed_object_source_accept6
    (MAP bounded_word64_object_q_cv radii) center_value
    center_gradient hessian
Proof
  strip_tac
  >> `object_domain` by
       fs
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_ordinary_accept6_def]
  >> `bounded_object_q_exact_packed_accept6 object_domain
        (MAP bounded_word64_object_q_cv radii) center_value
        center_gradient hessian` by
       metis_tac
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_packed_accept_word_radii]
  >> `object_domain = T` by simp []
  >> gvs []
  >> `bounded_object_q_exact_radius_pairs6_cv
        (MAP bounded_word64_object_q_cv radii) =
      SOME
        (MAP
          (\(left_radius,right_radius,twice).
            (bounded_word64_object_q_cv left_radius,
             bounded_word64_object_q_cv right_radius,twice))
          weights)` by
       metis_tac
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_radius_pairs_word_radii]
  >> `EVERY bounded_object_q_encoded
        (MAP bounded_word64_object_q_cv radii)` by
       simp
         [listTheory.EVERY_MAP,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
  >> Cases_on `word_result`
  >> fs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> `bounded_packed_q_interval_valid_cv center_value` by
       metis_tac [bounded_interval64_covers_packed_q_interval_valid_cv]
  >> `EVERY bounded_packed_q_interval_valid_cv center_gradient` by
       metis_tac
         [bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> `EVERY bounded_packed_q_interval_valid_cv hessian` by
       metis_tac
         [bounded_interval64_list_covers_packed_q_interval_valid_cv]
  >> metis_tac [bounded_object_q_exact_packed_accept_refines_source]
QED

Theorem bounded_case16594_packed_cell_source_accept6:
  bounded_packed_analytic_object_cell bounded_case16594_program
      bounded_case16594_prepared_program
      ((box_environment,center_environment,radii),certificates) ==>
  ?weights word_result object_domain center_value center_gradient
   gradient_bounds hessian.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_analytic64_program_eval radii center_environment box_environment
      bounded_case16594_prepared_program certificates = SOME word_result /\
    bounded_taylor64_covers_object_q word_result
      (BoundedObjectQTaylor object_domain center_value center_gradient
        (bounded_object_q_taylor_value_complete_cv center_value
          (bounded_object_q_taylor_error_cv radii center_gradient
            weights hessian))
        gradient_bounds hessian) /\
    bounded_packed_object_source_accept6
      (MAP bounded_word64_object_q_cv radii) center_value
      center_gradient hessian
Proof
  strip_tac
  >> drule
       compute_boundedCase16594OrdinaryAcceptBoundaryTheory.bounded_case16594_packed_cell_ordinary_accept6
  >> strip_tac
  >> rpt (first_assum $ irule_at Any)
  >> metis_tac [bounded_packed_object_ordinary_accept_refines_source]
QED

Theorem bounded_case16594_packed_cell_entry_eval:
  bounded_packed_analytic_object_cell bounded_case16594_program
      bounded_case16594_prepared_program
      ((box_environment,center_environment,radii),certificates) ==>
  ?center_value center_gradient hessian.
    compute_eval compute_default_clock bounded_packed_object_entry_ceqs
      (App «candle_cv_q_packed_object_accept6»
        [from_cv (Num 1);
         from_cv
           (bounded_object_q_cv_list
             (MAP bounded_word64_object_q_cv radii));
         from_cv center_value;
         from_cv (bounded_object_q_cv_list center_gradient);
         from_cv (bounded_object_q_cv_list hessian)]) (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_case16594_packed_cell_source_accept6
  >> qexists_tac `center_value`
  >> qexists_tac `center_gradient`
  >> qexists_tac `hessian`
  >> irule
       compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_entry_canonical_eval
  >> simp []
QED

val _ = export_theory ();
