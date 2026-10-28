(*****************************************************************************
 * Exact-rational bridge from the packed object completion to the ordinary
 * Candle six-dimensional acceptance arithmetic.
 *
 * The object checker accumulates from the left with scale-2^40 zero, whereas
 * the ordinary entry uses right-associated sums with canonical rational zero.
 * This theory relates their decoded rational values; it never assumes byte
 * equality between the two representations.
 *****************************************************************************)
Theory compute_boundedPackedObjectAcceptRefinement
Ancestors
  compute_boundedQFoldRelation
  compute_boundedPackedAnalyticNegativeBoundary
Libs
  bossLib preamble intLib

Definition bounded_object_q_dot_terms_cv_def:
  bounded_object_q_dot_terms_cv [] [] = [] /\
  bounded_object_q_dot_terms_cv [] (_::_) = [] /\
  bounded_object_q_dot_terms_cv (_::_) [] = [] /\
  bounded_object_q_dot_terms_cv (radius::radii) (entry::entries) =
    bounded_object_q_mul_cv
      (bounded_word64_object_q_cv radius)
      (bounded_object_q_interval_abs_upper_cv entry) ::
    bounded_object_q_dot_terms_cv radii entries
End

Definition bounded_object_q_quadratic_terms_cv_def:
  bounded_object_q_quadratic_terms_cv [] [] = [] /\
  bounded_object_q_quadratic_terms_cv [] (_::_) = [] /\
  bounded_object_q_quadratic_terms_cv (_::_) [] = [] /\
  bounded_object_q_quadratic_terms_cv
      ((left_radius,right_radius,double)::weights) (entry::entries) =
    bounded_object_q_quadratic_contribution_cv
      left_radius right_radius double entry ::
    bounded_object_q_quadratic_terms_cv weights entries
End

Definition bounded_object_q_ordinary_error_cv_def:
  bounded_object_q_ordinary_error_cv radii center_gradient weights hessian =
    let linear =
      bounded_object_q_right_sum_cv
        (bounded_object_q_dot_terms_cv radii center_gradient) in
    let quadratic =
      bounded_object_q_right_sum_cv
        (bounded_object_q_quadratic_terms_cv weights hessian) in
      bounded_object_q_add_cv
        (bounded_object_q_add_cv linear linear) quadratic
End

Definition bounded_object_q_ordinary_half_error_cv_def:
  bounded_object_q_ordinary_half_error_cv error =
    bounded_object_q_mul_cv
      (bounded_analytic_source_q_cv 1 0 1) error
End

Definition bounded_object_q_interval_upper_cv_def:
  bounded_object_q_interval_upper_cv (Pair lower upper) = upper /\
  bounded_object_q_interval_upper_cv _ = Num 0
End

Definition bounded_object_q_ordinary_value_upper_cv_def:
  bounded_object_q_ordinary_value_upper_cv center_value error =
    bounded_object_q_add_cv
      (bounded_object_q_interval_upper_cv center_value)
      (bounded_object_q_ordinary_half_error_cv error)
End

Definition bounded_object_q_strict_negative_cv_def:
  bounded_object_q_strict_negative_cv encoded <=>
    case bounded_object_q_ints encoded of
    | NONE => F
    | SOME (numerator,denominator) =>
        0 < denominator /\ numerator < 0
End

Theorem bounded_object_q_dot_acc_is_left_sum:
  !radii entries accumulator.
    LENGTH radii = LENGTH entries ==>
    bounded_object_q_dot_abs_upper_acc_cv radii entries accumulator =
      bounded_object_q_left_sum_cv
        (bounded_object_q_dot_terms_cv radii entries) accumulator
Proof
  Induct
  >> Cases_on `entries`
  >> simp
       [bounded_object_q_dot_terms_cv_def,
        bounded_object_q_left_sum_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_dot_abs_upper_acc_cv_def]
QED

Theorem bounded_object_q_quadratic_acc_is_left_sum:
  !weights entries accumulator.
    LENGTH weights = LENGTH entries ==>
    bounded_object_q_quadratic_abs_upper_acc_cv
        weights entries accumulator =
      bounded_object_q_left_sum_cv
        (bounded_object_q_quadratic_terms_cv weights entries) accumulator
Proof
  Induct
  >- (Cases_on `entries`
      >> simp
           [bounded_object_q_quadratic_terms_cv_def,
            bounded_object_q_left_sum_cv_def,
            compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
       [bounded_object_q_quadratic_terms_cv_def,
        bounded_object_q_left_sum_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def,
        LET_THM]
QED

Theorem bounded_object_q_word_zero_encoded:
  bounded_object_q_encoded (bounded_word64_object_q_cv 0w)
Proof
  simp
    [bounded_object_q_encoded_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_decodes]
QED

Theorem bounded_object_q_word_zero_equiv:
  bounded_case10173_q_cv_equiv
    (bounded_word64_object_q_cv 0w) bounded_object_q_zero_cv
Proof
  simp
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_decodes]
QED

Theorem bounded_object_q_dot_left_right_equiv:
  LENGTH radii = LENGTH entries /\
  EVERY bounded_object_q_encoded
    (bounded_object_q_dot_terms_cv radii entries) ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_dot_abs_upper_acc_cv radii entries
      (bounded_word64_object_q_cv 0w))
    (bounded_object_q_right_sum_cv
      (bounded_object_q_dot_terms_cv radii entries))
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_dot_acc_is_left_sum
  >> asm_rewrite_tac []
  >> irule bounded_object_q_left_right_zero_sum_cv_equiv
  >> simp [bounded_object_q_word_zero_encoded,
           bounded_object_q_word_zero_equiv]
QED

Theorem bounded_object_q_quadratic_left_right_equiv:
  LENGTH weights = LENGTH entries /\
  EVERY bounded_object_q_encoded
    (bounded_object_q_quadratic_terms_cv weights entries) ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_quadratic_abs_upper_acc_cv weights entries
      (bounded_word64_object_q_cv 0w))
    (bounded_object_q_right_sum_cv
      (bounded_object_q_quadratic_terms_cv weights entries))
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_quadratic_acc_is_left_sum
  >> asm_rewrite_tac []
  >> irule bounded_object_q_left_right_zero_sum_cv_equiv
  >> simp [bounded_object_q_word_zero_encoded,
           bounded_object_q_word_zero_equiv]
QED

Theorem bounded_object_q_ordinary_error_encoded:
  EVERY bounded_object_q_encoded
      (bounded_object_q_dot_terms_cv radii center_gradient) /\
  EVERY bounded_object_q_encoded
      (bounded_object_q_quadratic_terms_cv weights hessian) ==>
  bounded_object_q_encoded
    (bounded_object_q_ordinary_error_cv
      radii center_gradient weights hessian)
Proof
  strip_tac
  >> rw [bounded_object_q_ordinary_error_cv_def, LET_THM]
  >> irule bounded_object_q_add_cv_encoded
  >> conj_tac
  >- (irule bounded_object_q_add_cv_encoded
      >> simp [bounded_object_q_right_sum_cv_encoded])
  >> simp [bounded_object_q_right_sum_cv_encoded]
QED

Theorem bounded_object_q_object_error_ordinary_equiv:
  LENGTH radii = LENGTH center_gradient /\
  LENGTH weights = LENGTH hessian /\
  EVERY bounded_object_q_encoded
      (bounded_object_q_dot_terms_cv radii center_gradient) /\
  EVERY bounded_object_q_encoded
      (bounded_object_q_quadratic_terms_cv weights hessian) ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_taylor_error_cv
      radii center_gradient weights hessian)
    (bounded_object_q_ordinary_error_cv
      radii center_gradient weights hessian)
Proof
  strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_dot_abs_upper_acc_cv radii center_gradient
          (bounded_word64_object_q_cv 0w))
        (bounded_object_q_right_sum_cv
          (bounded_object_q_dot_terms_cv radii center_gradient))` by
       metis_tac [bounded_object_q_dot_left_right_equiv]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_quadratic_abs_upper_acc_cv weights hessian
          (bounded_word64_object_q_cv 0w))
        (bounded_object_q_right_sum_cv
          (bounded_object_q_quadratic_terms_cv weights hessian))` by
       metis_tac [bounded_object_q_quadratic_left_right_equiv]
  >> rw
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_error_cv_def,
        bounded_object_q_ordinary_error_cv_def, LET_THM]
  >> irule bounded_object_q_add_cv_equiv_cong
  >> simp []
  >> irule bounded_object_q_add_cv_equiv_cong
  >> simp []
QED

Theorem bounded_object_q_half_constant_encoded:
  bounded_object_q_encoded (bounded_analytic_source_q_cv 1 0 1)
Proof
  simp
    [bounded_object_q_encoded_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_decodes]
QED

Theorem bounded_object_q_half_error_ordinary_equiv:
  bounded_case10173_q_cv_equiv object_error ordinary_error /\
  bounded_object_q_encoded ordinary_error ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_half_cv object_error)
    (bounded_object_q_ordinary_half_error_cv ordinary_error)
Proof
  strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_analytic_source_q_cv 1 0 1)
        (bounded_analytic_source_q_cv 1 0 1)` by
       metis_tac [bounded_object_q_half_constant_encoded,
                  bounded_object_q_encoded_equiv_refl]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv object_error
          (bounded_analytic_source_q_cv 1 0 1))
        (bounded_object_q_mul_cv ordinary_error
          (bounded_analytic_source_q_cv 1 0 1))` by
       metis_tac [bounded_object_q_mul_cv_equiv_cong]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv ordinary_error
          (bounded_analytic_source_q_cv 1 0 1))
        (bounded_object_q_mul_cv
          (bounded_analytic_source_q_cv 1 0 1) ordinary_error)` by
       (irule bounded_object_q_mul_cv_comm_equiv
        >> simp [bounded_object_q_half_constant_encoded])
  >> fs
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_half_cv_def,
        bounded_object_q_ordinary_half_error_cv_def]
  >> metis_tac
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans]
QED

Theorem bounded_object_q_complete_value_upper:
  bounded_object_q_interval_upper_cv
    (bounded_object_q_taylor_value_complete_cv
      (Pair center_lower center_upper) error) =
  bounded_object_q_add_cv center_upper
    (bounded_object_q_half_cv error)
Proof
  simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_def,
     compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def,
     bounded_object_q_interval_upper_cv_def, LET_THM]
QED

Theorem bounded_object_q_complete_ordinary_value_upper_equiv:
  bounded_object_q_encoded center_upper /\
  bounded_case10173_q_cv_equiv object_error ordinary_error /\
  bounded_object_q_encoded ordinary_error ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_interval_upper_cv
      (bounded_object_q_taylor_value_complete_cv
        (Pair center_lower center_upper) object_error))
    (bounded_object_q_ordinary_value_upper_cv
      (Pair center_lower center_upper) ordinary_error)
Proof
  strip_tac
  >> rw [bounded_object_q_complete_value_upper,
         bounded_object_q_ordinary_value_upper_cv_def,
         bounded_object_q_interval_upper_cv_def]
  >> irule bounded_object_q_add_cv_equiv_cong
  >> simp [bounded_object_q_encoded_equiv_refl]
  >> irule bounded_object_q_half_error_ordinary_equiv
  >> simp []
QED

Theorem bounded_object_q_interval_upper_decodes:
  bounded_object_q_interval_ints object_interval =
      SOME ((lower_numerator,lower_denominator),
            (upper_numerator,upper_denominator)) ==>
  bounded_object_q_ints
    (bounded_object_q_interval_upper_cv object_interval) =
    SOME (upper_numerator,upper_denominator)
Proof
  Cases_on `object_interval`
  >> simp
       [bounded_object_q_interval_upper_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
QED

Theorem bounded_object_q_interval_negative_upper:
  bounded_object_q_interval_upper_strict_negative object_interval ==>
  bounded_object_q_strict_negative_cv
    (bounded_object_q_interval_upper_cv object_interval)
Proof
  rw
    [compute_boundedPackedAnalyticNegativeBoundaryTheory.bounded_object_q_interval_upper_strict_negative_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_q_interval_upper_decodes
  >> simp [bounded_object_q_strict_negative_cv_def]
QED

Theorem bounded_object_q_strict_negative_equiv:
  bounded_case10173_q_cv_equiv left right /\
  bounded_object_q_strict_negative_cv left ==>
  bounded_object_q_strict_negative_cv right
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints left`
  >- fs [bounded_object_q_strict_negative_cv_def]
  >> PairCases_on `x`
  >> Cases_on `bounded_object_q_ints right`
  >- fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> PairCases_on `x`
  >> fs
       [bounded_object_q_strict_negative_cv_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> conj_tac
  >- metis_tac
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> mp_tac
       (Q.INST
         [`left` |-> `left`, `right` |-> `right`,
          `left_numerator` |-> `x0`, `left_denominator` |-> `x1`,
          `right_numerator` |-> `x0'`, `right_denominator` |-> `x1'`]
         bounded_object_q_cv_equiv_strict_negative)
  >> impl_tac
  >- simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> simp []
QED

Definition bounded_object_q_interval_encoded_def:
  bounded_object_q_interval_encoded object_interval <=>
    ?decoded.
      bounded_object_q_interval_ints object_interval = SOME decoded
End

Theorem bounded_object_q_interval_encoded_shape:
  bounded_object_q_interval_encoded object_interval ==>
  ?lower upper.
    object_interval = Pair lower upper /\
    bounded_object_q_encoded lower /\
    bounded_object_q_encoded upper
Proof
  rw [bounded_object_q_interval_encoded_def]
  >> Cases_on `object_interval`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> simp [bounded_object_q_encoded_def]
QED

Theorem bounded_object_q_interval_abs_upper_encoded:
  bounded_object_q_interval_encoded object_interval ==>
  bounded_object_q_encoded
    (bounded_object_q_interval_abs_upper_cv object_interval)
Proof
  rw [bounded_object_q_interval_encoded_def,
      bounded_object_q_encoded_def]
  >> metis_tac
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_interval_abs_upper_cv_decodes]
QED

Theorem bounded_interval64_covers_object_q_encoded:
  bounded_interval64_covers_object_q word_interval object_interval ==>
  bounded_object_q_interval_encoded object_interval
Proof
  rw
    [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
     bounded_object_q_interval_encoded_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_interval64_list_covers_object_q_encoded:
  !word_intervals object_intervals.
    LIST_REL bounded_interval64_covers_object_q
      word_intervals object_intervals ==>
    EVERY bounded_object_q_interval_encoded object_intervals
Proof
  Induct
  >> Cases_on `object_intervals`
  >> simp [LIST_REL_def]
  >> metis_tac [bounded_interval64_covers_object_q_encoded]
QED

Theorem bounded_word64_object_q_encoded:
  bounded_object_q_encoded (bounded_word64_object_q_cv radius)
Proof
  simp
    [bounded_object_q_encoded_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_decodes]
QED

Theorem bounded_object_q_dot_terms_encoded:
  !radii entries.
    LENGTH radii = LENGTH entries /\
    EVERY bounded_object_q_interval_encoded entries ==>
    EVERY bounded_object_q_encoded
      (bounded_object_q_dot_terms_cv radii entries)
Proof
  Induct
  >> Cases_on `entries`
  >> simp [bounded_object_q_dot_terms_cv_def]
  >> metis_tac
       [bounded_object_q_mul_cv_encoded,
        bounded_word64_object_q_encoded,
        bounded_object_q_interval_abs_upper_encoded]
QED

Theorem bounded_object_q_quadratic_contribution_encoded:
  bounded_object_q_interval_encoded entry ==>
  bounded_object_q_encoded
    (bounded_object_q_quadratic_contribution_cv
      left_radius right_radius double entry)
Proof
  strip_tac
  >> `bounded_object_q_encoded
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv left_radius)
          (bounded_word64_object_q_cv right_radius))` by
       (irule bounded_object_q_mul_cv_encoded
        >> simp [bounded_word64_object_q_encoded])
  >> `bounded_object_q_encoded
        (bounded_object_q_mul_cv
          (bounded_object_q_mul_cv
            (bounded_word64_object_q_cv left_radius)
            (bounded_word64_object_q_cv right_radius))
          (bounded_object_q_interval_abs_upper_cv entry))` by
       (irule bounded_object_q_mul_cv_encoded
        >> simp [bounded_object_q_interval_abs_upper_encoded])
  >> Cases_on `double`
  >> simp
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_contribution_cv_def,
        LET_THM, bounded_object_q_add_cv_encoded]
QED

Theorem bounded_object_q_quadratic_terms_encoded:
  !weights entries.
    LENGTH weights = LENGTH entries /\
    EVERY bounded_object_q_interval_encoded entries ==>
    EVERY bounded_object_q_encoded
      (bounded_object_q_quadratic_terms_cv weights entries)
Proof
  Induct
  >- (Cases_on `entries`
      >> simp [bounded_object_q_quadratic_terms_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp [bounded_object_q_quadratic_terms_cv_def]
  >> metis_tac [bounded_object_q_quadratic_contribution_encoded]
QED

Theorem bounded_taylor_radius_pairs_lengths:
  bounded_taylor_radius_pairs radii = SOME weights ==>
  LENGTH radii = 6 /\ LENGTH weights = 21
Proof
  rw [compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def]
  >> every_case_tac
  >> gvs []
QED

Definition bounded_object_q_ordinary_accept6_def:
  bounded_object_q_ordinary_accept6 domain radii center_value
      center_gradient weights hessian <=>
    domain /\
    LENGTH radii = 6 /\
    LENGTH center_gradient = 6 /\
    LENGTH hessian = 21 /\
    bounded_object_q_strict_negative_cv
      (bounded_object_q_ordinary_value_upper_cv center_value
        (bounded_object_q_ordinary_error_cv
          radii center_gradient weights hessian))
End

Theorem bounded_object_q_completed_negative_implies_ordinary:
  bounded_object_q_interval_encoded center_value /\
  LENGTH radii = LENGTH center_gradient /\
  LENGTH weights = LENGTH hessian /\
  EVERY bounded_object_q_interval_encoded center_gradient /\
  EVERY bounded_object_q_interval_encoded hessian /\
  bounded_object_q_interval_upper_strict_negative
    (bounded_object_q_taylor_value_complete_cv center_value
      (bounded_object_q_taylor_error_cv
        radii center_gradient weights hessian)) ==>
  bounded_object_q_strict_negative_cv
    (bounded_object_q_ordinary_value_upper_cv center_value
      (bounded_object_q_ordinary_error_cv
        radii center_gradient weights hessian))
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_interval_encoded_shape
  >> gvs []
  >> `EVERY bounded_object_q_encoded
        (bounded_object_q_dot_terms_cv radii center_gradient)` by
       metis_tac [bounded_object_q_dot_terms_encoded]
  >> `EVERY bounded_object_q_encoded
        (bounded_object_q_quadratic_terms_cv weights hessian)` by
       metis_tac [bounded_object_q_quadratic_terms_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian)
        (bounded_object_q_ordinary_error_cv
          radii center_gradient weights hessian)` by
       metis_tac [bounded_object_q_object_error_ordinary_equiv]
  >> `bounded_object_q_encoded
        (bounded_object_q_ordinary_error_cv
          radii center_gradient weights hessian)` by
       metis_tac [bounded_object_q_ordinary_error_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_interval_upper_cv
          (bounded_object_q_taylor_value_complete_cv
            (Pair lower upper)
            (bounded_object_q_taylor_error_cv
              radii center_gradient weights hessian)))
        (bounded_object_q_ordinary_value_upper_cv
          (Pair lower upper)
          (bounded_object_q_ordinary_error_cv
            radii center_gradient weights hessian))` by
       metis_tac [bounded_object_q_complete_ordinary_value_upper_equiv]
  >> `bounded_object_q_strict_negative_cv
        (bounded_object_q_interval_upper_cv
          (bounded_object_q_taylor_value_complete_cv
            (Pair lower upper)
            (bounded_object_q_taylor_error_cv
              radii center_gradient weights hessian)))` by
       metis_tac [bounded_object_q_interval_negative_upper]
  >> metis_tac [bounded_object_q_strict_negative_equiv]
QED

Theorem bounded_packed_object_completed_negative_refines_ordinary_accept6:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_covers_object_q word_result
    (BoundedObjectQTaylor object_domain object_center_value
      object_center_gradient object_value_bound object_gradient_bounds
      object_hessian) /\
  bounded_taylor64_well_formed word_result /\
  object_domain /\
  bounded_object_q_interval_upper_strict_negative
    (bounded_object_q_taylor_value_complete_cv object_center_value
      (bounded_object_q_taylor_error_cv
        radii object_center_gradient weights object_hessian)) ==>
  bounded_object_q_ordinary_accept6 object_domain radii
    object_center_value object_center_gradient weights object_hessian
Proof
  Cases_on `word_result`
  >> strip_tac
  >> fs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> imp_res_tac bounded_taylor_radius_pairs_lengths
  >> imp_res_tac bounded_interval64_covers_object_q_encoded
  >> imp_res_tac bounded_interval64_list_covers_object_q_encoded
  >> imp_res_tac LIST_REL_LENGTH
  >> rw [bounded_object_q_ordinary_accept6_def]
  >> metis_tac [bounded_object_q_completed_negative_implies_ordinary]
QED

val _ = export_theory ();
