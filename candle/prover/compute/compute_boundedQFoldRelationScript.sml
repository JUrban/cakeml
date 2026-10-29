(*****************************************************************************
 * Representation-independent additive folds for exact object rationals.
 *****************************************************************************)
Theory compute_boundedQFoldRelation
Ancestors
  compute_boundedAnalyticObjectCompleteRefinement
  compute_boundedQRelationAlgebra
Libs
  bossLib preamble intLib

Definition bounded_object_q_encoded_def:
  bounded_object_q_encoded encoded <=>
    ?fraction. bounded_object_q_ints encoded = SOME fraction
End

Definition bounded_object_q_zero_cv_def:
  bounded_object_q_zero_cv = bounded_analytic_source_q_cv 0 0 0
End

Definition bounded_object_q_left_sum_cv_def:
  bounded_object_q_left_sum_cv [] accumulator = accumulator /\
  bounded_object_q_left_sum_cv (value::values) accumulator =
    bounded_object_q_left_sum_cv values
      (bounded_object_q_add_cv accumulator value)
End

Definition bounded_object_q_right_sum_cv_def:
  bounded_object_q_right_sum_cv [] = bounded_object_q_zero_cv /\
  bounded_object_q_right_sum_cv (value::values) =
    bounded_object_q_add_cv value
      (bounded_object_q_right_sum_cv values)
End

Theorem bounded_object_q_zero_cv_decodes[simp]:
  bounded_object_q_ints bounded_object_q_zero_cv =
    SOME ((&0:int),&1)
Proof
  simp [bounded_object_q_zero_cv_def]
QED

Theorem bounded_object_q_zero_cv_encoded[simp]:
  bounded_object_q_encoded bounded_object_q_zero_cv
Proof
  simp [bounded_object_q_encoded_def]
QED

Theorem bounded_object_q_add_cv_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right ==>
  bounded_object_q_encoded (bounded_object_q_add_cv left right)
Proof
  rw [bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> qexists_tac
       `(fraction0 * fraction'1 + fraction'0 * fraction1,
         fraction1 * fraction'1)`
  >> irule
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_cv_equiv_decodes:
  bounded_case10173_q_cv_equiv left right ==>
  ?left_numerator left_denominator right_numerator right_denominator.
    bounded_object_q_ints left =
      SOME (left_numerator,left_denominator) /\
    bounded_object_q_ints right =
      SOME (right_numerator,right_denominator) /\
    left_numerator * right_denominator =
      right_numerator * left_denominator
Proof
  rw
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_object_q_encoded_equiv_refl:
  bounded_object_q_encoded value ==>
  bounded_case10173_q_cv_equiv value value
Proof
  rw [bounded_object_q_encoded_def]
  >> metis_tac
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl]
QED

Theorem bounded_object_q_add_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left left' /\
  bounded_case10173_q_cv_equiv right right' ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_add_cv left right)
    (bounded_object_q_add_cv left' right')
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_cv_equiv_decodes
  >> rename1 `bounded_object_q_ints left = SOME (ln,ld)`
  >> rename1 `bounded_object_q_ints left' = SOME (ln2,ld2)`
  >> rename1 `bounded_object_q_ints right = SOME (rn,rd)`
  >> rename1 `bounded_object_q_ints right' = SOME (rn2,rd2)`
  >> mp_tac
       (Q.INST
          [`left` |-> `left`, `right` |-> `right`,
           `left_numerator` |-> `ln`, `left_denominator` |-> `ld`,
           `right_numerator` |-> `rn`, `right_denominator` |-> `rd`]
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes)
  >> impl_tac >- simp []
  >> strip_tac
  >> mp_tac
       (Q.INST
          [`left` |-> `left'`, `right` |-> `right'`,
           `left_numerator` |-> `ln2`, `left_denominator` |-> `ld2`,
           `right_numerator` |-> `rn2`, `right_denominator` |-> `rd2`]
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes)
  >> impl_tac >- simp []
  >> strip_tac
  >> gvs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> `(ln * rd) * (ld2 * rd2) =
      (ln2 * rd2) * (ld * rd)` by
       metis_tac
         [integerTheory.INT_MUL_ASSOC, integerTheory.INT_MUL_COMM]
  >> `(rn * ld) * (ld2 * rd2) =
      (rn2 * ld2) * (ld * rd)` by
       metis_tac
         [integerTheory.INT_MUL_ASSOC, integerTheory.INT_MUL_COMM]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_q_add_cv_assoc_equiv:
  bounded_object_q_encoded first_value /\
  bounded_object_q_encoded second_value /\
  bounded_object_q_encoded third_value ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_add_cv
      (bounded_object_q_add_cv first_value second_value) third_value)
    (bounded_object_q_add_cv first_value
      (bounded_object_q_add_cv second_value third_value))
Proof
  rw [bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> PairCases_on `fraction''`
  >> rename1 `bounded_object_q_ints first_value = SOME (fnumer,fdenom)`
  >> rename1 `bounded_object_q_ints second_value = SOME (snumer,sdenom)`
  >> rename1 `bounded_object_q_ints third_value = SOME (tnumer,tdenom)`
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv first_value second_value) =
      SOME
        (fnumer * sdenom + snumer * fdenom,
         fdenom * sdenom)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv second_value third_value) =
      SOME
        (snumer * tdenom + tnumer * sdenom,
         sdenom * tdenom)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv
          (bounded_object_q_add_cv first_value second_value) third_value) =
      SOME
        ((fnumer * sdenom + snumer * fdenom) * tdenom +
           tnumer * (fdenom * sdenom),
         (fdenom * sdenom) * tdenom)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv first_value
          (bounded_object_q_add_cv second_value third_value)) =
      SOME
        (fnumer * (sdenom * tdenom) +
           (snumer * tdenom + tnumer * sdenom) * fdenom,
         fdenom * (sdenom * tdenom))` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> INT_RING_TAC
QED

Theorem bounded_object_q_add_cv_zero_right_equiv:
  bounded_object_q_encoded value ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_add_cv value bounded_object_q_zero_cv) value
Proof
  rw [bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv value bounded_object_q_zero_cv) =
      SOME (fraction0 * (&1:int) + (&0:int) * fraction1,
        fraction1 * (&1:int))` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
QED

Theorem bounded_object_q_add_cv_zero_left_equiv:
  bounded_object_q_encoded value ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_add_cv bounded_object_q_zero_cv value) value
Proof
  rw [bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv bounded_object_q_zero_cv value) =
      SOME ((&0:int) * fraction1 + fraction0 * (&1:int),
        (&1:int) * fraction1)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
QED

Theorem bounded_object_q_mul_cv_encoded:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right ==>
  bounded_object_q_encoded (bounded_object_q_mul_cv left right)
Proof
  rw [bounded_object_q_encoded_def]
  >> metis_tac
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes]
QED

Theorem bounded_object_q_fraction_mul_equiv:
  (left_numerator:int) * left_denominator' =
      left_numerator' * left_denominator /\
  right_numerator * right_denominator' =
      right_numerator' * right_denominator ==>
  (left_numerator * right_numerator) *
      (left_denominator' * right_denominator') =
    (left_numerator' * right_numerator') *
      (left_denominator * right_denominator)
Proof
  strip_tac
  >> `(left_numerator * right_numerator) *
        (left_denominator' * right_denominator') =
      (left_numerator * left_denominator') *
        (right_numerator * right_denominator')` by INT_RING_TAC
  >> `(left_numerator' * right_numerator') *
        (left_denominator * right_denominator) =
      (left_numerator' * left_denominator) *
        (right_numerator' * right_denominator)` by INT_RING_TAC
  >> metis_tac []
QED

Theorem bounded_object_q_mul_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left left' /\
  bounded_case10173_q_cv_equiv right right' ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_mul_cv left right)
    (bounded_object_q_mul_cv left' right')
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_cv_equiv_decodes
  >> rename1 `bounded_object_q_ints left = SOME (ln,ld)`
  >> rename1 `bounded_object_q_ints left' = SOME (ln2,ld2)`
  >> rename1 `bounded_object_q_ints right = SOME (rn,rd)`
  >> rename1 `bounded_object_q_ints right' = SOME (rn2,rd2)`
  >> `bounded_object_q_ints (bounded_object_q_mul_cv left right) =
      SOME (ln * rn,ld * rd)` by
       (mp_tac
          (Q.INST
            [`left` |-> `left`, `right` |-> `right`,
             `left_fraction` |-> `(ln,ld)`,
             `right_fraction` |-> `(rn,rd)`]
            compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv left' right') =
      SOME (ln2 * rn2,ld2 * rd2)` by
       (mp_tac
          (Q.INST
            [`left` |-> `left'`, `right` |-> `right'`,
             `left_fraction` |-> `(ln2,ld2)`,
             `right_fraction` |-> `(rn2,rd2)`]
            compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> irule bounded_object_q_fraction_mul_equiv
  >> simp []
QED

Theorem bounded_object_q_mul_cv_comm_equiv:
  bounded_object_q_encoded left /\
  bounded_object_q_encoded right ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_mul_cv left right)
    (bounded_object_q_mul_cv right left)
Proof
  rw [bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> `bounded_object_q_ints (bounded_object_q_mul_cv left right) =
      SOME (fraction0 * fraction'0,fraction1 * fraction'1)` by
       (mp_tac
          (Q.INST
            [`left` |-> `left`, `right` |-> `right`,
             `left_fraction` |-> `(fraction0,fraction1)`,
             `right_fraction` |-> `(fraction'0,fraction'1)`]
            compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv right left) =
      SOME (fraction'0 * fraction0,fraction'1 * fraction1)` by
       (mp_tac
          (Q.INST
            [`left` |-> `right`, `right` |-> `left`,
             `left_fraction` |-> `(fraction'0,fraction'1)`,
             `right_fraction` |-> `(fraction0,fraction1)`]
            compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes)
        >> simp
             [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def])
  >> simp
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> INT_RING_TAC
QED

Theorem bounded_object_q_cv_equiv_strict_negative:
  bounded_case10173_q_cv_equiv left right /\
  bounded_object_q_ints left = SOME (left_numerator,left_denominator) /\
  bounded_object_q_ints right = SOME (right_numerator,right_denominator) ==>
  (left_numerator < 0 <=> right_numerator < 0)
Proof
  strip_tac
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> `0 < left_denominator` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `0 < right_denominator` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> eq_tac
  >- (strip_tac
      >> `left_numerator * right_denominator < 0` by
           (qsuff_tac
              `0 < -left_numerator * right_denominator`
            >- intLib.ARITH_TAC
            >> irule
                 (REWRITE_RULE [integerTheory.INT_0]
                   integerTheory.INT_LT_MUL)
            >> intLib.ARITH_TAC)
      >> CCONTR_TAC
      >> `0 <= right_numerator * left_denominator` by
           (irule integerTheory.INT_LE_MUL
            >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> `right_numerator * left_denominator < 0` by
       (qsuff_tac
          `0 < -right_numerator * left_denominator`
        >- intLib.ARITH_TAC
        >> irule
             (REWRITE_RULE [integerTheory.INT_0]
               integerTheory.INT_LT_MUL)
        >> intLib.ARITH_TAC)
  >> CCONTR_TAC
  >> `0 <= left_numerator * right_denominator` by
       (irule integerTheory.INT_LE_MUL
        >> intLib.ARITH_TAC)
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_q_right_sum_cv_encoded:
  !values.
    EVERY bounded_object_q_encoded values ==>
    bounded_object_q_encoded (bounded_object_q_right_sum_cv values)
Proof
  Induct
  >> simp
       [bounded_object_q_right_sum_cv_def,
        bounded_object_q_add_cv_encoded]
QED

Theorem bounded_object_q_left_sum_cv_encoded:
  !values accumulator.
    EVERY bounded_object_q_encoded values /\
    bounded_object_q_encoded accumulator ==>
    bounded_object_q_encoded
      (bounded_object_q_left_sum_cv values accumulator)
Proof
  Induct
  >> simp
       [bounded_object_q_left_sum_cv_def,
        bounded_object_q_add_cv_encoded]
QED

Theorem bounded_object_q_left_right_sum_cv_equiv:
  !values accumulator.
    EVERY bounded_object_q_encoded values /\
    bounded_object_q_encoded accumulator ==>
    bounded_case10173_q_cv_equiv
      (bounded_object_q_left_sum_cv values accumulator)
      (bounded_object_q_add_cv accumulator
        (bounded_object_q_right_sum_cv values))
Proof
  Induct
  >- (rw [bounded_object_q_left_sum_cv_def,
          bounded_object_q_right_sum_cv_def]
      >> irule
           compute_boundedQRelationAlgebraTheory.bounded_case10173_q_cv_equiv_sym
      >> irule bounded_object_q_add_cv_zero_right_equiv
      >> simp [])
  >> rpt gen_tac
  >> strip_tac
  >> fs [bounded_object_q_left_sum_cv_def,
         bounded_object_q_right_sum_cv_def]
  >> `bounded_object_q_encoded
        (bounded_object_q_add_cv accumulator h)` by
       metis_tac [bounded_object_q_add_cv_encoded]
  >> `bounded_object_q_encoded
        (bounded_object_q_right_sum_cv values)` by
       metis_tac [bounded_object_q_right_sum_cv_encoded]
  >> qpat_x_assum `!accumulator'. _`
       (mp_tac o Q.SPEC `bounded_object_q_add_cv accumulator h`)
  >> impl_tac >- simp []
  >> strip_tac
  >> irule
       compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
  >> qexists_tac
       `bounded_object_q_add_cv
          (bounded_object_q_add_cv accumulator h)
          (bounded_object_q_right_sum_cv values)`
  >> simp []
  >> irule bounded_object_q_add_cv_assoc_equiv
  >> simp []
QED

Theorem bounded_object_q_left_right_zero_sum_cv_equiv:
  EVERY bounded_object_q_encoded values /\
  bounded_object_q_encoded accumulator /\
  bounded_case10173_q_cv_equiv accumulator bounded_object_q_zero_cv ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_left_sum_cv values accumulator)
    (bounded_object_q_right_sum_cv values)
Proof
  strip_tac
  >> `bounded_object_q_encoded
        (bounded_object_q_right_sum_cv values)` by
       metis_tac [bounded_object_q_right_sum_cv_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_right_sum_cv values)
        (bounded_object_q_right_sum_cv values)` by
       metis_tac [bounded_object_q_encoded_equiv_refl]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_add_cv accumulator
          (bounded_object_q_right_sum_cv values))
        (bounded_object_q_add_cv bounded_object_q_zero_cv
          (bounded_object_q_right_sum_cv values))` by
       metis_tac [bounded_object_q_add_cv_equiv_cong]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_add_cv bounded_object_q_zero_cv
          (bounded_object_q_right_sum_cv values))
        (bounded_object_q_right_sum_cv values)` by
       metis_tac [bounded_object_q_add_cv_zero_left_equiv]
  >> metis_tac
       [bounded_object_q_left_right_sum_cv_equiv,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans]
QED

val _ = export_theory ();
