(*****************************************************************************
 * Zero-preservation lemmas for representation-independent object-q Taylor
 * arithmetic.
 *
 * Object-q operations deliberately retain unnormalised denominators.  These
 * lemmas state the algebraic zero facts through the rational equivalence
 * relation, so semantic bridge proofs do not expand large closed numerals.
 *****************************************************************************)
open compute_boundedObjectTaylorEquivalenceTheory
open compute_boundedPackedObjectAcceptRefinementTheory
open preamble

Theory compute_boundedObjectTaylorZeroAlgebra
Ancestors
  compute_boundedObjectTaylorEquivalence
  compute_boundedPackedObjectAcceptRefinement
Libs
  bossLib preamble intLib

Theorem bounded_object_q_zero_equiv_of_decodes:
  bounded_object_q_ints value = SOME ((&0:int),denominator) ==>
  bounded_case10173_q_cv_equiv
    value (bounded_analytic_source_q_cv 0 0 0)
Proof
  rw
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
QED

Theorem bounded_object_q_interval_zero_equiv_of_decodes:
  bounded_object_q_interval_ints value =
      SOME (((&0:int),lower_denominator),((&0:int),upper_denominator)) ==>
  bounded_object_q_interval_cv_equiv value
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  Cases_on `value`
  >- simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> simp
    [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def]
  >> metis_tac [bounded_object_q_zero_equiv_of_decodes]
QED

Theorem bounded_analytic_source_q_cv_encoded[simp]:
  bounded_object_q_encoded
    (bounded_analytic_source_q_cv positive negative
      denominator_predecessor)
Proof
  simp
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
QED

Theorem bounded_analytic_source_q_interval_cv_encoded[simp]:
  bounded_object_q_interval_encoded
    (bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor)
Proof
  simp
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
QED

Theorem bounded_object_q_interval_neg_cv_encoded:
  bounded_object_q_interval_encoded value ==>
  bounded_object_q_interval_encoded (bounded_object_q_interval_neg_cv value)
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> qexists_tac `bounded_object_q_interval_neg_ints decoded`
  >> irule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_interval_add_cv_encoded:
  bounded_object_q_interval_encoded left /\
  bounded_object_q_interval_encoded right ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_interval_add_cv left right)
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> qexists_tac `bounded_object_q_interval_add_ints decoded decoded'`
  >> irule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_interval_mul_cv_encoded:
  bounded_object_q_interval_encoded left /\
  bounded_object_q_interval_encoded right ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_interval_mul_cv left right)
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> qexists_tac `bounded_object_q_interval_mul_ints decoded decoded'`
  >> irule
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_decodes
  >> simp []
QED


Theorem bounded_object_q_neg_cv_encoded:
  bounded_object_q_encoded value ==>
  bounded_object_q_encoded (bounded_object_q_neg_cv value)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> qexists_tac `(-fraction0,fraction1)`
  >> irule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_interval_pair_encoded:
  bounded_object_q_encoded lower /\
  bounded_object_q_encoded upper ==>
  bounded_object_q_interval_encoded (Pair lower upper)
Proof
  rw
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> qexists_tac `(fraction,fraction')`
  >> simp []
QED

Theorem bounded_object_q_dot_abs_upper_acc_cv_encoded:
  !radii entries accumulator.
    LENGTH radii = LENGTH entries /\
    EVERY bounded_object_q_interval_encoded entries /\
    bounded_object_q_encoded accumulator ==>
    bounded_object_q_encoded
      (bounded_object_q_dot_abs_upper_acc_cv radii entries accumulator)
Proof
  Induct
  >> Cases_on `entries`
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_dot_abs_upper_acc_cv_def]
  >> metis_tac
    [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
     compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_abs_upper_encoded]
QED

Theorem bounded_object_q_quadratic_abs_upper_acc_cv_encoded:
  !weights entries accumulator.
    LENGTH weights = LENGTH entries /\
    EVERY bounded_object_q_interval_encoded entries /\
    bounded_object_q_encoded accumulator ==>
    bounded_object_q_encoded
      (bounded_object_q_quadratic_abs_upper_acc_cv
        weights entries accumulator)
Proof
  Induct
  >- (Cases_on `entries`
      >> simp
        [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def]
  >> metis_tac
    [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_quadratic_contribution_encoded]
QED

Theorem bounded_object_q_taylor_error_cv_encoded:
  LENGTH radii = LENGTH center_gradient /\
  LENGTH weights = LENGTH hessian /\
  EVERY bounded_object_q_interval_encoded center_gradient /\
  EVERY bounded_object_q_interval_encoded hessian ==>
  bounded_object_q_encoded
    (bounded_object_q_taylor_error_cv
      radii center_gradient weights hessian)
Proof
  strip_tac
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_error_cv_def,
     LET_THM]
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded
  >> conj_tac
  >- (irule
        compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded
      >> metis_tac
        [bounded_object_q_dot_abs_upper_acc_cv_encoded,
         compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded])
  >> metis_tac
    [bounded_object_q_quadratic_abs_upper_acc_cv_encoded,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
QED

Theorem bounded_object_q_half_cv_encoded:
  bounded_object_q_encoded value ==>
  bounded_object_q_encoded (bounded_object_q_half_cv value)
Proof
  strip_tac
  >> rw
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_half_cv_def]
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded
  >> simp []
QED

Theorem bounded_object_q_symmetric_half_interval_cv_encoded:
  bounded_object_q_encoded error ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_symmetric_half_interval_cv error)
Proof
  strip_tac
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_def,
     LET_THM]
  >> irule bounded_object_q_interval_pair_encoded
  >> metis_tac
    [bounded_object_q_half_cv_encoded,
     bounded_object_q_neg_cv_encoded]
QED

Theorem bounded_object_q_taylor_value_complete_cv_encoded:
  bounded_object_q_interval_encoded center /\
  bounded_object_q_encoded error ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_taylor_value_complete_cv center error)
Proof
  strip_tac
  >> rw
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def]
  >> irule bounded_object_q_interval_add_cv_encoded
  >> simp [bounded_object_q_symmetric_half_interval_cv_encoded]
QED


Theorem bounded_object_q_taylor_gradient_row_complete_cv_encoded:
  bounded_object_q_interval_encoded center_entry /\
  LENGTH radii = LENGTH hessian_row /\
  EVERY bounded_object_q_interval_encoded hessian_row ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_taylor_gradient_row_complete_cv center_entry
      (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
        (bounded_word64_object_q_cv 0w)))
Proof
  strip_tac
  >> rw
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_row_complete_cv_def]
  >> irule bounded_object_q_taylor_value_complete_cv_encoded
  >> simp []
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_encoded
  >> metis_tac
    [bounded_object_q_dot_abs_upper_acc_cv_encoded,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
QED

Theorem bounded_object_q_taylor_gradient_rows_complete_cv_encoded:
  !center_gradient rows.
    LENGTH radii = 6 /\
    LENGTH center_gradient = LENGTH rows /\
    EVERY bounded_object_q_interval_encoded center_gradient /\
    EVERY
      (\row.
        LENGTH row = 6 /\
        EVERY bounded_object_q_interval_encoded row) rows ==>
    EVERY bounded_object_q_interval_encoded
      (bounded_object_q_taylor_gradient_rows_complete_cv
        radii center_gradient rows)
Proof
  Induct_on `center_gradient`
  >> Cases_on `rows`
  >> simp
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_rows_complete_cv_def]
  >> metis_tac [bounded_object_q_taylor_gradient_row_complete_cv_encoded]
QED

Theorem bounded_hessian64_rows_encoded:
  bounded_hessian64_rows hessian = SOME rows /\
  EVERY bounded_object_q_interval_encoded hessian ==>
  LENGTH rows = 6 /\
  EVERY
    (\row.
      LENGTH row = 6 /\
      EVERY bounded_object_q_interval_encoded row) rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_q_taylor_gradient_complete_cv_encoded:
  LENGTH radii = 6 /\
  LENGTH center_gradient = 6 /\
  LENGTH hessian = 21 /\
  EVERY bounded_object_q_interval_encoded center_gradient /\
  EVERY bounded_object_q_interval_encoded hessian ==>
  EVERY bounded_object_q_interval_encoded
    (bounded_object_q_taylor_gradient_complete_cv
      radii center_gradient hessian)
Proof
  strip_tac
  >> rw
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_complete_cv_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_hessian64_rows_encoded
  >> irule bounded_object_q_taylor_gradient_rows_complete_cv_encoded
  >> simp []
QED

Theorem bounded_hessian64_rows_length21:
  LENGTH hessian = 21 ==>
  ?rows.
    bounded_hessian64_rows hessian = SOME rows /\
    LENGTH rows = 6
Proof
  rw
    [listTheory.LENGTH_EQ_NUM_compute,
     compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> simp [listTheory.LENGTH_EQ_NUM_compute]
QED

Theorem bounded_object_q_taylor_gradient_rows_complete_cv_length:
  !center_gradient rows.
    LENGTH center_gradient = LENGTH rows ==>
    LENGTH
      (bounded_object_q_taylor_gradient_rows_complete_cv
        radii center_gradient rows) =
    LENGTH center_gradient
Proof
  Induct
  >> Cases_on `rows`
  >> simp
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_rows_complete_cv_def]
QED

Theorem bounded_object_q_taylor_gradient_complete_cv_length6:
  LENGTH center_gradient = 6 /\
  LENGTH hessian = 21 ==>
  LENGTH
    (bounded_object_q_taylor_gradient_complete_cv
      radii center_gradient hessian) = 6
Proof
  strip_tac
  >> drule bounded_hessian64_rows_length21
  >> strip_tac
  >> rw
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_complete_cv_def]
  >> gvs [bounded_object_q_taylor_gradient_rows_complete_cv_length]
QED

Theorem bounded_object_q_symmetric_product_pairs_cv_length6:
  LENGTH left = 6 /\
  LENGTH right = 6 ==>
  LENGTH (bounded_object_q_symmetric_product_pairs_cv left right) = 21
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def]
QED

Theorem bounded_object_q_interval_fused_scale_add_cv_length6:
  LENGTH left = 6 /\
  LENGTH right = 6 ==>
  LENGTH
    (bounded_object_q_interval_fused_scale_add_cv
      left_scale left right_scale right) = 6
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
QED

Theorem bounded_object_q_interval_fused_hessian_cv_length21:
  LENGTH left_hessian = 21 /\
  LENGTH right_hessian = 21 /\
  LENGTH outer = 21 ==>
  LENGTH
    (bounded_object_q_interval_fused_hessian_cv
      left_value right_value left_hessian right_hessian outer) = 21
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def]
QED

Definition bounded_object_q_decodes_zero_def:
  bounded_object_q_decodes_zero value <=>
    ?denominator.
      bounded_object_q_ints value = SOME ((&0:int),denominator)
End

Theorem bounded_analytic_source_q_zero_decodes_zero[simp]:
  bounded_object_q_decodes_zero (bounded_analytic_source_q_cv 0 0 0)
Proof
  simp [bounded_object_q_decodes_zero_def]
QED

Theorem bounded_word64_object_q_zero_decodes_zero[simp]:
  bounded_object_q_decodes_zero (bounded_word64_object_q_cv 0w)
Proof
  simp
    [bounded_object_q_decodes_zero_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_decodes]
QED

Theorem bounded_object_q_decodes_zero_encoded:
  bounded_object_q_decodes_zero value ==>
  bounded_object_q_encoded value
Proof
  rw
    [bounded_object_q_decodes_zero_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> metis_tac []
QED

Theorem bounded_object_q_add_decodes_zero:
  bounded_object_q_decodes_zero left /\
  bounded_object_q_decodes_zero right ==>
  bounded_object_q_decodes_zero (bounded_object_q_add_cv left right)
Proof
  rw [bounded_object_q_decodes_zero_def]
  >> `bounded_object_q_ints (bounded_object_q_add_cv left right) =
      SOME
        ((&0:int) * denominator' + (&0:int) * denominator,
         denominator * denominator')` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> qexists_tac `denominator * denominator'`
  >> gvs []
QED

Theorem bounded_object_q_mul_right_decodes_zero:
  bounded_object_q_encoded left /\
  bounded_object_q_decodes_zero right ==>
  bounded_object_q_decodes_zero (bounded_object_q_mul_cv left right)
Proof
  rw
    [bounded_object_q_decodes_zero_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> `bounded_object_q_ints (bounded_object_q_mul_cv left right) =
      SOME
        (bounded_int_fraction_mul
          (fraction0,fraction1) ((&0:int),denominator))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes
        >> simp [])
  >> qexists_tac `fraction1 * denominator`
  >> gvs
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
QED

Theorem bounded_object_q_mul_left_decodes_zero:
  bounded_object_q_decodes_zero left /\
  bounded_object_q_encoded right ==>
  bounded_object_q_decodes_zero (bounded_object_q_mul_cv left right)
Proof
  rw
    [bounded_object_q_decodes_zero_def,
     compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> `bounded_object_q_ints (bounded_object_q_mul_cv left right) =
      SOME
        (bounded_int_fraction_mul
          ((&0:int),denominator) (fraction0,fraction1))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes
        >> simp [])
  >> qexists_tac `denominator * fraction1`
  >> gvs
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
QED

Theorem bounded_object_q_interval_abs_upper_decodes_zero:
  bounded_object_q_interval_ints value =
      SOME (((&0:int),lower_denominator),((&0:int),upper_denominator)) ==>
  bounded_object_q_decodes_zero
    (bounded_object_q_interval_abs_upper_cv value)
Proof
  strip_tac
  >> rw [bounded_object_q_decodes_zero_def]
  >> qexists_tac `upper_denominator`
  >> `bounded_object_q_ints
        (bounded_object_q_interval_abs_upper_cv value) =
      SOME
        (bounded_int_fraction_interval_abs_upper
          (((&0:int),lower_denominator),((&0:int),upper_denominator)))` by
       (irule
          compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_interval_abs_upper_cv_decodes
        >> simp [])
  >> gvs
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_interval_abs_upper_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_abs_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_int_fraction_neg_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Definition bounded_object_q_interval_decodes_zero_def:
  bounded_object_q_interval_decodes_zero value <=>
    ?lower_denominator upper_denominator.
      bounded_object_q_interval_ints value =
        SOME (((&0:int),lower_denominator),((&0:int),upper_denominator))
End

Theorem bounded_analytic_source_q_zero_interval_decodes_zero[simp]:
  bounded_object_q_interval_decodes_zero
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  simp
    [bounded_object_q_interval_decodes_zero_def,
     compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_analytic_source_q_zero_interval_cv_decodes]
QED

Theorem bounded_object_q_interval_decodes_zero_encoded:
  bounded_object_q_interval_decodes_zero value ==>
  bounded_object_q_interval_encoded value
Proof
  rw
    [bounded_object_q_interval_decodes_zero_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> metis_tac []
QED

Theorem bounded_object_q_interval_add_decodes_zero:
  bounded_object_q_interval_decodes_zero left /\
  bounded_object_q_interval_decodes_zero right ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_interval_add_cv left right)
Proof
  rw [bounded_object_q_interval_decodes_zero_def]
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_add_cv left right) =
      SOME
        (bounded_object_q_interval_add_ints
          (((&0:int),lower_denominator),((&0:int),upper_denominator))
          (((&0:int),lower_denominator'),((&0:int),upper_denominator')))` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_decodes
        >> simp [])
  >> qexists_tac `lower_denominator * lower_denominator'`
  >> qexists_tac `upper_denominator * upper_denominator'`
  >> gvs
    [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_interval_add_ints_def]
QED

Theorem bounded_object_q_dot_abs_upper_acc_decodes_zero:
  !radii entries accumulator.
    LENGTH radii = LENGTH entries /\
    EVERY bounded_object_q_interval_decodes_zero entries /\
    bounded_object_q_decodes_zero accumulator ==>
    bounded_object_q_decodes_zero
      (bounded_object_q_dot_abs_upper_acc_cv radii entries accumulator)
Proof
  Induct
  >> Cases_on `entries`
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_dot_abs_upper_acc_cv_def]
  >> rpt strip_tac
  >> first_x_assum irule
  >> simp []
  >> irule bounded_object_q_add_decodes_zero
  >> simp []
  >> irule bounded_object_q_mul_right_decodes_zero
  >> simp []
  >> conj_tac
  >- (fs [bounded_object_q_interval_decodes_zero_def]
      >> metis_tac [bounded_object_q_interval_abs_upper_decodes_zero])
  >> simp
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
QED

Theorem bounded_object_q_quadratic_raw_decodes_zero:
  bounded_object_q_interval_decodes_zero entry ==>
  bounded_object_q_decodes_zero
    (bounded_object_q_mul_cv
      (bounded_object_q_mul_cv
        (bounded_word64_object_q_cv left_radius)
        (bounded_word64_object_q_cv right_radius))
      (bounded_object_q_interval_abs_upper_cv entry))
Proof
  strip_tac
  >> irule bounded_object_q_mul_right_decodes_zero
  >> conj_tac
  >- (fs [bounded_object_q_interval_decodes_zero_def]
      >> metis_tac [bounded_object_q_interval_abs_upper_decodes_zero])
  >> irule compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_encoded
  >> simp
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
QED

Theorem bounded_object_q_quadratic_contribution_decodes_zero:
  bounded_object_q_interval_decodes_zero entry ==>
  bounded_object_q_decodes_zero
    (bounded_object_q_quadratic_contribution_cv
      left_radius right_radius double entry)
Proof
  strip_tac
  >> Cases_on `double`
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_contribution_cv_def,
     LET_THM,
     bounded_object_q_quadratic_raw_decodes_zero,
     bounded_object_q_add_decodes_zero]
QED

Theorem bounded_object_q_quadratic_abs_upper_acc_decodes_zero:
  !weights entries accumulator.
    LENGTH weights = LENGTH entries /\
    EVERY bounded_object_q_interval_decodes_zero entries /\
    bounded_object_q_decodes_zero accumulator ==>
    bounded_object_q_decodes_zero
      (bounded_object_q_quadratic_abs_upper_acc_cv
        weights entries accumulator)
Proof
  Induct
  >- (Cases_on `entries`
      >> simp
        [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def]
  >> rpt strip_tac
  >> first_x_assum irule
  >> simp []
  >> irule bounded_object_q_add_decodes_zero
  >> simp [bounded_object_q_quadratic_contribution_decodes_zero]
QED

Theorem bounded_object_q_taylor_error_decodes_zero:
  LENGTH radii = LENGTH center_gradient /\
  LENGTH weights = LENGTH hessian /\
  EVERY bounded_object_q_interval_decodes_zero center_gradient /\
  EVERY bounded_object_q_interval_decodes_zero hessian ==>
  bounded_object_q_decodes_zero
    (bounded_object_q_taylor_error_cv
      radii center_gradient weights hessian)
Proof
  strip_tac
  >> simp
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_error_cv_def,
     LET_THM]
  >> irule bounded_object_q_add_decodes_zero
  >> conj_tac
  >- (irule bounded_object_q_add_decodes_zero
      >> simp []
      >> irule bounded_object_q_dot_abs_upper_acc_decodes_zero
      >> simp [])
  >> irule bounded_object_q_quadratic_abs_upper_acc_decodes_zero
  >> simp []
QED

Theorem bounded_object_q_symmetric_half_interval_decodes_zero:
  bounded_object_q_decodes_zero error ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_symmetric_half_interval_cv error)
Proof
  rw
    [bounded_object_q_decodes_zero_def,
     bounded_object_q_interval_decodes_zero_def]
  >> qexists_tac `denominator * (&2:int)`
  >> qexists_tac `denominator * (&2:int)`
  >> mp_tac
       (Q.INST
         [`numerator` |-> `(&0:int)`,
          `denominator` |-> `denominator`,
          `error` |-> `error`]
         compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_decodes)
  >> simp []
QED

Theorem bounded_object_q_taylor_value_complete_decodes_zero:
  bounded_object_q_interval_decodes_zero center /\
  bounded_object_q_decodes_zero error ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_value_complete_cv center error)
Proof
  rw
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def]
  >> irule bounded_object_q_interval_add_decodes_zero
  >> simp [bounded_object_q_symmetric_half_interval_decodes_zero]
QED

Theorem bounded_object_q_taylor_gradient_row_complete_decodes_zero:
  bounded_object_q_interval_decodes_zero center_entry /\
  bounded_object_q_decodes_zero variation ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_gradient_row_complete_cv
      center_entry variation)
Proof
  rw
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_row_complete_cv_def]
  >> irule bounded_object_q_taylor_value_complete_decodes_zero
  >> simp [bounded_object_q_add_decodes_zero]
QED

Theorem bounded_hessian64_rows_decodes_zero:
  bounded_hessian64_rows hessian = SOME rows /\
  EVERY bounded_object_q_interval_decodes_zero hessian ==>
  LENGTH rows = 6 /\
  EVERY
    (\row.
      LENGTH row = 6 /\
      EVERY bounded_object_q_interval_decodes_zero row) rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_q_taylor_gradient_rows_complete_decodes_zero:
  !center_gradient rows.
    LENGTH radii = 6 /\
    LENGTH center_gradient = LENGTH rows /\
    EVERY bounded_object_q_interval_decodes_zero center_gradient /\
    EVERY
      (\row.
        LENGTH row = 6 /\
        EVERY bounded_object_q_interval_decodes_zero row) rows ==>
    EVERY bounded_object_q_interval_decodes_zero
      (bounded_object_q_taylor_gradient_rows_complete_cv
        radii center_gradient rows)
Proof
  Induct
  >> Cases_on `rows`
  >> simp
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_rows_complete_cv_def]
  >> rpt strip_tac
  >> irule bounded_object_q_taylor_gradient_row_complete_decodes_zero
  >> simp []
  >> irule bounded_object_q_dot_abs_upper_acc_decodes_zero
  >> simp []
QED

Theorem bounded_object_q_taylor_gradient_complete_decodes_zero:
  LENGTH radii = 6 /\
  LENGTH center_gradient = 6 /\
  LENGTH hessian = 21 /\
  EVERY bounded_object_q_interval_decodes_zero center_gradient /\
  EVERY bounded_object_q_interval_decodes_zero hessian ==>
  EVERY bounded_object_q_interval_decodes_zero
    (bounded_object_q_taylor_gradient_complete_cv
      radii center_gradient hessian)
Proof
  strip_tac
  >> drule bounded_hessian64_rows_length21
  >> strip_tac
  >> `LENGTH rows = 6 /\
      EVERY
        (\row.
          LENGTH row = 6 /\
          EVERY bounded_object_q_interval_decodes_zero row) rows` by
       metis_tac [bounded_hessian64_rows_decodes_zero]
  >> rw
    [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_complete_cv_def]
  >> gvs []
  >> irule bounded_object_q_taylor_gradient_rows_complete_decodes_zero
  >> simp []
QED

Theorem bounded_object_q_interval_decodes_zero_equiv:
  bounded_object_q_interval_decodes_zero value ==>
  bounded_object_q_interval_cv_equiv value
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  rw [bounded_object_q_interval_decodes_zero_def]
  >> metis_tac [bounded_object_q_interval_zero_equiv_of_decodes]
QED

Theorem bounded_object_q_interval_neg_decodes_zero:
  bounded_object_q_interval_decodes_zero value ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_interval_neg_cv value)
Proof
  rw [bounded_object_q_interval_decodes_zero_def]
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_neg_cv value) =
      SOME
        (bounded_object_q_interval_neg_ints
          (((&0:int),lower_denominator),((&0:int),upper_denominator)))` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_decodes
        >> simp [])
  >> qexists_tac `upper_denominator`
  >> qexists_tac `lower_denominator`
  >> gvs
    [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_interval_neg_ints_def]
QED

Theorem bounded_object_q_interval_mul_left_decodes_zero:
  bounded_object_q_interval_decodes_zero left /\
  bounded_object_q_interval_encoded right ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_interval_mul_cv left right)
Proof
  rw
    [bounded_object_q_interval_decodes_zero_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> PairCases_on `decoded`
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_mul_cv left right) =
      SOME
        (bounded_object_q_interval_mul_ints
          (((&0:int),lower_denominator),((&0:int),upper_denominator))
          ((decoded0,decoded1),(decoded2,decoded3)))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_decodes
        >> simp [])
  >> qexists_tac `lower_denominator * decoded1`
  >> qexists_tac `upper_denominator * decoded3`
  >> gvs
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_ints_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_min4_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max4_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_min_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_object_q_interval_mul_right_decodes_zero:
  bounded_object_q_interval_encoded left /\
  bounded_object_q_interval_decodes_zero right ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_interval_mul_cv left right)
Proof
  rw
    [bounded_object_q_interval_decodes_zero_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> PairCases_on `decoded`
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_mul_cv left right) =
      SOME
        (bounded_object_q_interval_mul_ints
          ((decoded0,decoded1),(decoded2,decoded3))
          (((&0:int),lower_denominator),((&0:int),upper_denominator)))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_decodes
        >> simp [])
  >> qexists_tac `decoded1 * lower_denominator`
  >> qexists_tac `decoded3 * upper_denominator`
  >> gvs
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_ints_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_min4_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max4_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_min_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED


Definition bounded_object_q_product_input_decodes_zero_def:
  bounded_object_q_product_input_decodes_zero (left,right) <=>
    (bounded_object_q_interval_decodes_zero left /\
     bounded_object_q_interval_encoded right) \/
    (bounded_object_q_interval_encoded left /\
     bounded_object_q_interval_decodes_zero right)
End

Definition bounded_object_q_fused_pair_decodes_zero_def:
  bounded_object_q_fused_pair_decodes_zero (first,second) <=>
    bounded_object_q_product_input_decodes_zero first /\
    bounded_object_q_product_input_decodes_zero second
End

Theorem bounded_object_q_product_input_mul_decodes_zero:
  bounded_object_q_product_input_decodes_zero input ==>
  bounded_object_q_interval_decodes_zero
    (bounded_object_q_interval_mul_cv (FST input) (SND input))
Proof
  PairCases_on `input`
  >> rw [bounded_object_q_product_input_decodes_zero_def]
  >> metis_tac
    [bounded_object_q_interval_mul_left_decodes_zero,
     bounded_object_q_interval_mul_right_decodes_zero]
QED

Theorem bounded_object_q_interval_products_sum_acc_decodes_zero:
  !inputs accumulator.
    EVERY bounded_object_q_product_input_decodes_zero inputs /\
    bounded_object_q_interval_decodes_zero accumulator ==>
    bounded_object_q_interval_decodes_zero
      (bounded_object_q_interval_products_sum_acc_cv inputs accumulator)
Proof
  Induct
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> rpt strip_tac
  >> first_x_assum irule
  >> simp []
  >> irule bounded_object_q_interval_add_decodes_zero
  >> simp [bounded_object_q_product_input_mul_decodes_zero]
QED

Theorem bounded_object_q_interval_fused_scale_add_decodes_zero:
  !left right.
    bounded_object_q_interval_encoded left_scale /\
    bounded_object_q_interval_encoded right_scale /\
    EVERY bounded_object_q_interval_decodes_zero left /\
    EVERY bounded_object_q_interval_decodes_zero right ==>
    EVERY bounded_object_q_interval_decodes_zero
      (bounded_object_q_interval_fused_scale_add_cv
        left_scale left right_scale right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule bounded_object_q_interval_products_sum_acc_decodes_zero
  >> simp
    [bounded_object_q_product_input_decodes_zero_def,
     bounded_object_q_interval_decodes_zero_encoded]
QED

Theorem bounded_object_q_symmetric_product_pairs_row_decodes_zero:
  !left right.
    bounded_object_q_interval_decodes_zero fixed_left /\
    bounded_object_q_interval_encoded fixed_right /\
    EVERY bounded_object_q_interval_decodes_zero left /\
    EVERY bounded_object_q_interval_encoded right ==>
    EVERY bounded_object_q_fused_pair_decodes_zero
      (bounded_object_q_symmetric_product_pairs_row_cv
        fixed_left fixed_right left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def,
     bounded_object_q_fused_pair_decodes_zero_def,
     bounded_object_q_product_input_decodes_zero_def]
  >> metis_tac
    [bounded_object_q_interval_decodes_zero_encoded]
QED

Theorem bounded_object_q_symmetric_product_pairs_decodes_zero:
  !left right.
    EVERY bounded_object_q_interval_decodes_zero left /\
    EVERY bounded_object_q_interval_encoded right ==>
    EVERY bounded_object_q_fused_pair_decodes_zero
      (bounded_object_q_symmetric_product_pairs_cv left right)
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule bounded_object_q_symmetric_product_pairs_row_decodes_zero
  >> simp []
QED

Theorem bounded_object_q_interval_fused_hessian_decodes_zero:
  !left_hessian right_hessian outer.
    bounded_object_q_interval_encoded left_value /\
    bounded_object_q_interval_encoded right_value /\
    EVERY bounded_object_q_interval_decodes_zero left_hessian /\
    EVERY bounded_object_q_interval_decodes_zero right_hessian /\
    EVERY bounded_object_q_fused_pair_decodes_zero outer ==>
    EVERY bounded_object_q_interval_decodes_zero
      (bounded_object_q_interval_fused_hessian_cv
        left_value right_value left_hessian right_hessian outer)
Proof
  Induct_on `left_hessian`
  >> Cases_on `right_hessian`
  >> Cases_on `outer`
  >> simp
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def]
  >> rpt gen_tac
  >> strip_tac
  >> PairCases_on `h'`
  >> irule bounded_object_q_interval_products_sum_acc_decodes_zero
  >> simp
    [bounded_object_q_fused_pair_decodes_zero_def,
     bounded_object_q_product_input_decodes_zero_def,
     bounded_object_q_interval_decodes_zero_encoded]
  >> fs
    [bounded_object_q_fused_pair_decodes_zero_def,
     bounded_object_q_product_input_decodes_zero_def]
QED

Theorem bounded_object_q_interval_zero_list_rel:
  !values.
    EVERY bounded_object_q_interval_decodes_zero values ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (REPLICATE (LENGTH values)
        (bounded_analytic_source_q_interval_cv 0 0 0))
      values
Proof
  Induct
  >> simp [LIST_REL_def]
  >> metis_tac
    [bounded_object_q_interval_cv_equiv_sym,
     bounded_object_q_interval_decodes_zero_equiv]
QED


Theorem bounded_object_q_interval_mul_zero_right_decodes:
  bounded_object_q_interval_ints value =
      SOME ((lower_numerator,lower_denominator),
            (upper_numerator,upper_denominator)) ==>
  bounded_object_q_interval_ints
      (bounded_object_q_interval_mul_cv value
        (bounded_analytic_source_q_interval_cv 0 0 0)) =
    SOME (((&0:int),lower_denominator),((&0:int),upper_denominator))
Proof
  strip_tac
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_mul_cv value
          (bounded_analytic_source_q_interval_cv 0 0 0)) =
      SOME
        (bounded_object_q_interval_mul_ints
          ((lower_numerator,lower_denominator),
           (upper_numerator,upper_denominator))
          (((&0:int),&1),((&0:int),&1)))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_decodes
        >> simp
          [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_analytic_source_q_zero_interval_cv_decodes])
  >> gvs
    [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_ints_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_min4_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max4_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_min_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_object_q_interval_mul_zero_right_equiv:
  bounded_object_q_interval_encoded value ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_mul_cv value
      (bounded_analytic_source_q_interval_cv 0 0 0))
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  rw
    [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
  >> PairCases_on `decoded`
  >> irule bounded_object_q_interval_zero_equiv_of_decodes
  >> metis_tac [bounded_object_q_interval_mul_zero_right_decodes]
QED

Theorem bounded_object_q_add_right_decodes_zero_equiv:
  bounded_object_q_encoded value /\
  bounded_object_q_decodes_zero zero ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_add_cv value zero) value
Proof
  rw
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
     bounded_object_q_decodes_zero_def]
  >> PairCases_on `fraction`
  >> `bounded_object_q_ints (bounded_object_q_add_cv value zero) =
      SOME
        (fraction0 * denominator + (&0:int) * fraction1,
         fraction1 * denominator)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> simp
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> INT_RING_TAC
QED

Theorem bounded_object_q_interval_add_right_decodes_zero_equiv:
  bounded_object_q_interval_encoded value /\
  bounded_object_q_interval_decodes_zero zero ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_add_cv value zero) value
Proof
  strip_tac
  >> drule
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> strip_tac
  >> drule bounded_object_q_interval_decodes_zero_encoded
  >> strip_tac
  >> drule
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> strip_tac
  >> gvs
    [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def,
     compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
     bounded_object_q_interval_decodes_zero_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> conj_tac
  >> irule bounded_object_q_add_right_decodes_zero_equiv
  >> simp
    [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def,
     bounded_object_q_decodes_zero_def]
QED

Theorem bounded_object_q_taylor_value_complete_zero_equiv:
  bounded_object_q_interval_encoded center /\
  bounded_object_q_decodes_zero error ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_taylor_value_complete_cv center error) center
Proof
  rw
    [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def]
  >> irule bounded_object_q_interval_add_right_decodes_zero_equiv
  >> simp [bounded_object_q_symmetric_half_interval_decodes_zero]
QED

val _ = export_theory ();
