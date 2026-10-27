(*****************************************************************************
 * Source-rational bridge from generic scale-2^40 preparation to the
 * existing Candle object-q interval contract.
 *
 * This is the first semantic seam above structural plan refinement.  It
 * proves that a successfully prepared constant encloses the exact canonical
 * source rational expected by the object-level checker; no rounded object
 * value or case-specific constant table is introduced.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectRefinement
Ancestors
  compute_boundedAnalyticPreparedPlanSound
  compute_boundedObjectIntervalRelation compute_boundedTaylorBase
Libs
  bossLib preamble intLib

Definition bounded_analytic_source_q_cv_def:
  bounded_analytic_source_q_cv positive negative denominator_predecessor =
    Pair (Pair (Num positive) (Num negative))
      (Num denominator_predecessor)
End

Definition bounded_analytic_source_q_interval_cv_def:
  bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor =
    Pair
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor)
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor)
End

Definition bounded_taylor64_covers_object_q_state_def:
  bounded_taylor64_covers_object_q_state
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian)
      object_domain object_center_value object_center_gradient
      object_value_bound object_gradient_bounds object_hessian <=>
    domain = object_domain /\
    bounded_interval64_covers_object_q center_value object_center_value /\
    LIST_REL bounded_interval64_covers_object_q
      center_gradient object_center_gradient /\
    bounded_interval64_covers_object_q value_bound object_value_bound /\
    LIST_REL bounded_interval64_covers_object_q
      gradient_bounds object_gradient_bounds /\
    LIST_REL bounded_interval64_covers_object_q hessian object_hessian
End

Definition bounded_object_q_nth_def:
  bounded_object_q_nth [] index = NONE /\
  bounded_object_q_nth (value::rest) 0 = SOME value /\
  bounded_object_q_nth (value::rest) (SUC index) =
    bounded_object_q_nth rest index
End

Definition bounded_object_q_unit_vector_def:
  bounded_object_q_unit_vector index =
    GENLIST
      (\position.
         if position = index then
           bounded_analytic_source_q_interval_cv 1 0 0
         else bounded_analytic_source_q_interval_cv 0 0 0)
      6
End

Definition bounded_object_q_interval_neg_ints_def:
  bounded_object_q_interval_neg_ints
      (((lower_numerator,lower_denominator),
        (upper_numerator,upper_denominator)) :
          (int # int) # (int # int)) =
    ((-upper_numerator,upper_denominator),
     (-lower_numerator,lower_denominator))
End

Definition bounded_object_q_interval_add_ints_def:
  bounded_object_q_interval_add_ints
      (((left_lower_numerator,left_lower_denominator),
        (left_upper_numerator,left_upper_denominator)) :
          (int # int) # (int # int))
      (((right_lower_numerator,right_lower_denominator),
        (right_upper_numerator,right_upper_denominator)) :
          (int # int) # (int # int)) =
    (((left_lower_numerator * right_lower_denominator) +
       (right_lower_numerator * left_lower_denominator),
      left_lower_denominator * right_lower_denominator),
     ((left_upper_numerator * right_upper_denominator) +
       (right_upper_numerator * left_upper_denominator),
      left_upper_denominator * right_upper_denominator))
End

Theorem bounded_analytic_source_q_cv_decodes[simp]:
  bounded_object_q_ints
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor) =
    SOME ((&positive:int) - &negative,
          &(SUC denominator_predecessor):int)
Proof
  simp [bounded_analytic_source_q_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem bounded_analytic_rational_constant64_covers_object_q:
  bounded_analytic_rational_constant64 positive negative
      denominator_predecessor = SOME interval ==>
  bounded_interval64_covers_object_q interval
    (Pair
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor)
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
Proof
  strip_tac
  >> drule bounded_analytic_rational_constant64_covers
  >> rw [bounded_analytic_rational_interval_covers_def,
         compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def,
         compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
         bounded_analytic_source_q_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
         compute_boundedObjectIntervalRelationTheory.bounded_word_scale_int_def,
         compute_boundedAnalyticRationalConstantTheory.bounded_analytic_scale40_def]
QED

Theorem bounded_interval64_zero_covers_object_q_zero:
  bounded_interval64_covers_object_q bounded_interval64_zero
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_atan_one_covers_object_q_one:
  bounded_interval64_covers_object_q bounded_atan_one
    (bounded_analytic_source_q_interval_cv 1 0 0)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_zeros_cover_object_q_zeros:
  LIST_REL bounded_interval64_covers_object_q
    (bounded_interval64_zeros (n:num))
    (REPLICATE n (bounded_analytic_source_q_interval_cv 0 0 0))
Proof
  Induct_on `n`
  >> simp [compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def,
           bounded_interval64_zero_covers_object_q_zero]
QED

Theorem bounded_interval64_nth_covers_object_q_nth:
  !word_values object_values index word_value.
    LIST_REL bounded_interval64_covers_object_q
      word_values object_values /\
    bounded_interval64_nth word_values index = SOME word_value ==>
    ?object_value.
      bounded_object_q_nth object_values index = SOME object_value /\
      bounded_interval64_covers_object_q word_value object_value
Proof
  Induct_on `word_values`
  >> Cases_on `object_values`
  >> Cases_on `index`
  >> rw [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
         bounded_object_q_nth_def]
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_interval64_unit_vector_covers_object_q:
  bounded_interval64_unit_vector index = SOME gradient ==>
  LIST_REL bounded_interval64_covers_object_q gradient
    (bounded_object_q_unit_vector index)
Proof
  rw [compute_boundedTaylorBaseTheory.bounded_interval64_unit_vector_def,
      bounded_object_q_unit_vector_def]
  >> gvs [LIST_REL_EL_EQN]
  >> rw []
  >> Cases_on `n = index`
  >> simp [bounded_atan_one_covers_object_q_one,
           bounded_interval64_zero_covers_object_q_zero]
QED

Theorem bounded_taylor64_constant_covers_source_q:
  bounded_analytic_rational_constant64 positive negative
      denominator_predecessor = SOME interval /\
  bounded_taylor64_constant interval = SOME result ==>
  bounded_taylor64_covers_object_q_state result T
    (bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor)
    (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0))
    (bounded_analytic_source_q_interval_cv positive negative
      denominator_predecessor)
    (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0))
    (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0))
Proof
  strip_tac
  >> imp_res_tac bounded_analytic_rational_constant64_covers
  >> `bounded_interval64_valid interval` by
       fs [bounded_analytic_rational_interval_covers_def]
  >> fs [compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def,
         compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
         compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def,
         compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def]
  >> gvs [bounded_taylor64_covers_object_q_state_def]
  >> simp [bounded_analytic_source_q_interval_cv_def,
           bounded_interval64_zeros_cover_object_q_zeros,
           bounded_analytic_rational_constant64_covers_object_q]
QED

Theorem bounded_taylor64_variable_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor64_variable center_environment box_environment index =
    SOME result ==>
  ?object_center object_box.
    bounded_object_q_nth object_center_environment index =
      SOME object_center /\
    bounded_object_q_nth object_box_environment index = SOME object_box /\
    bounded_taylor64_covers_object_q_state result T object_center
      (bounded_object_q_unit_vector index) object_box
      (bounded_object_q_unit_vector index)
      (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0))
Proof
  strip_tac
  >> fs [compute_boundedTaylorBaseTheory.bounded_taylor64_variable_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_interval64_nth_covers_object_q_nth
  >> imp_res_tac bounded_interval64_unit_vector_covers_object_q
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_make_def]
  >> every_case_tac
  >> gvs [bounded_taylor64_covers_object_q_state_def]
  >> metis_tac [bounded_interval64_zeros_cover_object_q_zeros]
QED

Theorem bounded_interval64_neg_covers_object_q_ints:
  bounded_interval64_covers_object_q_ints source object_interval ==>
  bounded_interval64_covers_object_q_ints
    (bounded_interval64_neg source)
    (bounded_object_q_interval_neg_ints object_interval)
Proof
  PairCases_on `object_interval`
  >> rw [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
         bounded_object_q_interval_neg_ints_def]
  >> simp [compute_boundedIntervalAddTheory.bounded_interval64_neg_value,
           integerTheory.INT_MUL_LNEG, integerTheory.INT_MUL_RNEG]
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_interval_add_ordered:
  0 < (left_lower_denominator:int) /\
  0 < left_upper_denominator /\
  left_lower_numerator * left_upper_denominator <=
    left_upper_numerator * left_lower_denominator /\
  0 < right_lower_denominator /\
  0 < right_upper_denominator /\
  right_lower_numerator * right_upper_denominator <=
    right_upper_numerator * right_lower_denominator ==>
  (left_lower_numerator * right_lower_denominator +
   right_lower_numerator * left_lower_denominator) *
      (left_upper_denominator * right_upper_denominator) <=
    (left_upper_numerator * right_upper_denominator +
     right_upper_numerator * left_upper_denominator) *
      (left_lower_denominator * right_lower_denominator)
Proof
  strip_tac
  >> `0 < right_lower_denominator * right_upper_denominator` by
       (irule
          (REWRITE_RULE [integerTheory.INT_0]
            integerTheory.INT_LT_MUL)
        >> fs [])
  >> `0 < left_lower_denominator * left_upper_denominator` by
       (irule
          (REWRITE_RULE [integerTheory.INT_0]
            integerTheory.INT_LT_MUL)
        >> fs [])
  >> `(right_lower_denominator * right_upper_denominator) *
        (left_lower_numerator * left_upper_denominator) <=
      (right_lower_denominator * right_upper_denominator) *
        (left_upper_numerator * left_lower_denominator)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> fs [])
  >> `(left_lower_denominator * left_upper_denominator) *
        (right_lower_numerator * right_upper_denominator) <=
      (left_lower_denominator * left_upper_denominator) *
        (right_upper_numerator * right_lower_denominator)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> fs [])
  >> `(left_lower_numerator * right_lower_denominator +
       right_lower_numerator * left_lower_denominator) *
        (left_upper_denominator * right_upper_denominator) =
      (right_lower_denominator * right_upper_denominator) *
        (left_lower_numerator * left_upper_denominator) +
      (left_lower_denominator * left_upper_denominator) *
        (right_lower_numerator * right_upper_denominator)` by INT_RING_TAC
  >> `(left_upper_numerator * right_upper_denominator +
       right_upper_numerator * left_upper_denominator) *
        (left_lower_denominator * right_lower_denominator) =
      (right_lower_denominator * right_upper_denominator) *
        (left_upper_numerator * left_lower_denominator) +
      (left_lower_denominator * left_upper_denominator) *
        (right_upper_numerator * right_lower_denominator)` by INT_RING_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_add_lower_bound:
  0 < (left_denominator:int) /\
  0 < right_denominator /\
  left_denominator * left_value <= scale * left_numerator /\
  right_denominator * right_value <= scale * right_numerator ==>
  left_denominator * right_denominator * (left_value + right_value) <=
    scale *
      (left_numerator * right_denominator +
       right_numerator * left_denominator)
Proof
  strip_tac
  >> `right_denominator * (left_denominator * left_value) <=
      right_denominator * (scale * left_numerator)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> conj_tac >- fs []
        >> intLib.ARITH_TAC)
  >> `left_denominator * (right_denominator * right_value) <=
      left_denominator * (scale * right_numerator)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> conj_tac >- fs []
        >> intLib.ARITH_TAC)
  >> `left_denominator * right_denominator *
        (left_value + right_value) =
      right_denominator * (left_denominator * left_value) +
      left_denominator * (right_denominator * right_value)` by INT_RING_TAC
  >> `scale *
        (left_numerator * right_denominator +
         right_numerator * left_denominator) =
      right_denominator * (scale * left_numerator) +
      left_denominator * (scale * right_numerator)` by INT_RING_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_add_upper_bound:
  0 < (left_denominator:int) /\
  0 < right_denominator /\
  scale * left_numerator <= left_denominator * left_value /\
  scale * right_numerator <= right_denominator * right_value ==>
  scale *
      (left_numerator * right_denominator +
       right_numerator * left_denominator) <=
    left_denominator * right_denominator * (left_value + right_value)
Proof
  strip_tac
  >> `right_denominator * (scale * left_numerator) <=
      right_denominator * (left_denominator * left_value)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> conj_tac >- fs []
        >> intLib.ARITH_TAC)
  >> `left_denominator * (scale * right_numerator) <=
      left_denominator * (right_denominator * right_value)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> conj_tac >- fs []
        >> intLib.ARITH_TAC)
  >> `scale *
        (left_numerator * right_denominator +
         right_numerator * left_denominator) =
      right_denominator * (scale * left_numerator) +
      left_denominator * (scale * right_numerator)` by INT_RING_TAC
  >> `left_denominator * right_denominator *
        (left_value + right_value) =
      right_denominator * (left_denominator * left_value) +
      left_denominator * (right_denominator * right_value)` by INT_RING_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_add_covers_object_q_ints:
  bounded_interval64_covers_object_q_ints
      left
      ((left_lower_numerator,left_lower_denominator),
       (left_upper_numerator,left_upper_denominator)) /\
  bounded_interval64_covers_object_q_ints
      right
      ((right_lower_numerator,right_lower_denominator),
       (right_upper_numerator,right_upper_denominator)) /\
  bounded_interval64_add left right = SOME result ==>
  bounded_interval64_covers_object_q_ints result
    (bounded_object_q_interval_add_ints
      ((left_lower_numerator,left_lower_denominator),
       (left_upper_numerator,left_upper_denominator))
      ((right_lower_numerator,right_lower_denominator),
       (right_upper_numerator,right_upper_denominator)))
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> fs [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
         bounded_object_q_interval_add_ints_def]
  >> rpt conj_tac
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> fs [])
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> fs [])
  >- metis_tac [bounded_int_fraction_interval_add_ordered]
  >- metis_tac [bounded_int_fraction_add_lower_bound]
  >> metis_tac [bounded_int_fraction_add_upper_bound]
QED

val _ = export_theory ();
