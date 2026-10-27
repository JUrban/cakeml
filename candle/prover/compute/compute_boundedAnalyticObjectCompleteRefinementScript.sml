(*****************************************************************************
 * Object-q refinement for compact Taylor completion.
 *
 * The completion arithmetic works with unsigned absolute-error accumulators.
 * This theory starts the semantic bridge by relating the executable absolute
 * upper bound of a scale-2^40 interval to the exact rational absolute upper
 * bound used by the object-q Taylor contract.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectCompleteRefinement
Ancestors
  compute_boundedAnalyticObjectFusedProductRefinement
Libs
  bossLib preamble intLib

Definition bounded_int_fraction_neg_def:
  bounded_int_fraction_neg ((numerator,denominator):int # int) =
    (-numerator,denominator)
End

Definition bounded_int_fraction_abs_def:
  bounded_int_fraction_abs fraction =
    bounded_int_fraction_max fraction
      (bounded_int_fraction_neg fraction)
End

Definition bounded_int_fraction_interval_abs_upper_def:
  bounded_int_fraction_interval_abs_upper (lower,upper) =
    bounded_int_fraction_max
      (bounded_int_fraction_abs lower)
      (bounded_int_fraction_abs upper)
End

Definition bounded_object_q_abs_cv_def:
  bounded_object_q_abs_cv source =
    bounded_object_q_max_cv source
      (bounded_object_q_neg_cv source)
End

Definition bounded_object_q_interval_abs_upper_cv_def:
  bounded_object_q_interval_abs_upper_cv (Pair lower upper) =
    bounded_object_q_max_cv
      (bounded_object_q_abs_cv lower)
      (bounded_object_q_abs_cv upper) /\
  bounded_object_q_interval_abs_upper_cv _ = Num 0
End

Definition bounded_word64_upper_covers_int_fraction_def:
  bounded_word64_upper_covers_int_fraction magnitude
      ((numerator,denominator):int # int) <=>
    0 < denominator /\
    (&1099511627776:int) * numerator <=
      denominator * &(w2n magnitude)
End

Definition bounded_word64_upper_covers_object_q_def:
  bounded_word64_upper_covers_object_q magnitude encoded <=>
    case bounded_object_q_ints encoded of
    | NONE => F
    | SOME fraction =>
        bounded_word64_upper_covers_int_fraction magnitude fraction
End

Definition bounded_object_q_nonnegative_def:
  bounded_object_q_nonnegative encoded <=>
    case bounded_object_q_ints encoded of
    | NONE => F
    | SOME (numerator,denominator) =>
        0 < denominator /\ 0 <= numerator
End

Definition bounded128_upper_covers_int_fraction_def:
  bounded128_upper_covers_int_fraction magnitude
      ((numerator,denominator):int # int) <=>
    0 < denominator /\
    (&1208925819614629174706176:int) * numerator <=
      denominator * &(bounded128_to_num magnitude)
End

Definition bounded128_upper_covers_object_q_def:
  bounded128_upper_covers_object_q magnitude encoded <=>
    case bounded_object_q_ints encoded of
    | NONE => F
    | SOME fraction =>
        bounded128_upper_covers_int_fraction magnitude fraction
End

Theorem bounded_object_q_abs_cv_decodes:
  bounded_object_q_ints source = SOME fraction ==>
  bounded_object_q_ints (bounded_object_q_abs_cv source) =
    SOME (bounded_int_fraction_abs fraction)
Proof
  strip_tac
  >> `bounded_object_q_ints (bounded_object_q_neg_cv source) =
        SOME (bounded_int_fraction_neg fraction)` by
       (PairCases_on `fraction`
        >> simp [bounded_int_fraction_neg_def]
        >> irule
             compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_decodes
        >> simp [])
  >> rw [bounded_object_q_abs_cv_def, bounded_int_fraction_abs_def]
  >> irule
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_interval_abs_upper_cv_decodes:
  bounded_object_q_interval_ints source = SOME object_interval ==>
  bounded_object_q_ints
      (bounded_object_q_interval_abs_upper_cv source) =
    SOME (bounded_int_fraction_interval_abs_upper object_interval)
Proof
  Cases_on `source`
  >> rw [bounded_object_q_interval_abs_upper_cv_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs [bounded_object_q_interval_abs_upper_cv_def]
  >> `bounded_object_q_ints (bounded_object_q_abs_cv c) =
        SOME (bounded_int_fraction_abs lower')` by
       metis_tac [bounded_object_q_abs_cv_decodes]
  >> `bounded_object_q_ints (bounded_object_q_abs_cv c0) =
        SOME (bounded_int_fraction_abs upper')` by
       metis_tac [bounded_object_q_abs_cv_decodes]
  >> fs [bounded_int_fraction_interval_abs_upper_def]
  >> irule
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max_cv_decodes
  >> simp []
QED

Theorem bounded_signed64_magnitude_bounds:
  -&(w2n (bounded_signed64_magnitude value)) <=
      bounded_signed64_to_int value /\
  bounded_signed64_to_int value <=
      &(w2n (bounded_signed64_magnitude value))
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> simp [compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
QED

Theorem bounded_interval64_abs_upper_magnitude_bounds:
  w2n
      (bounded_signed64_magnitude
        (bounded_interval64_lower interval)) <=
    w2n (bounded_interval64_abs_upper interval) /\
  w2n
      (bounded_signed64_magnitude
        (bounded_interval64_upper interval)) <=
    w2n (bounded_interval64_abs_upper interval)
Proof
  Cases_on `interval`
  >> rw [compute_boundedTaylorCompleteTheory.bounded_interval64_abs_upper_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def,
         LET_THM]
  >> Cases_on
       `word_lo (bounded_signed64_magnitude b)
          (bounded_signed64_magnitude b0)`
  >> fs [WORD_LO]
QED

Theorem bounded_interval64_abs_upper_fraction_bounds:
  bounded_interval64_contains_int_fraction interval
      (numerator,denominator) /\
  0 < denominator ==>
  (&1099511627776:int) * numerator <=
      denominator * &(w2n (bounded_interval64_abs_upper interval)) /\
  (&1099511627776:int) * -numerator <=
      denominator * &(w2n (bounded_interval64_abs_upper interval))
Proof
  strip_tac
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_contains_int_fraction_def]
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded_interval64_lower interval`]
          bounded_signed64_magnitude_bounds)
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded_interval64_upper interval`]
          bounded_signed64_magnitude_bounds)
  >> assume_tac
       (Q.INST [`interval` |-> `interval`]
          bounded_interval64_abs_upper_magnitude_bounds)
  >> `bounded_signed64_to_int (bounded_interval64_upper interval) <=
        &(w2n (bounded_interval64_abs_upper interval))` by
       (simp [integerTheory.INT_OF_NUM_LE]
        >> intLib.ARITH_TAC)
  >> `-bounded_signed64_to_int (bounded_interval64_lower interval) <=
        &(w2n (bounded_interval64_abs_upper interval))` by
       (simp [integerTheory.INT_OF_NUM_LE]
        >> intLib.ARITH_TAC)
  >> `denominator *
        bounded_signed64_to_int (bounded_interval64_upper interval) <=
      denominator * &(w2n (bounded_interval64_abs_upper interval))` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp []
        >> intLib.ARITH_TAC)
  >> `denominator *
        -bounded_signed64_to_int (bounded_interval64_lower interval) <=
      denominator * &(w2n (bounded_interval64_abs_upper interval))` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp []
        >> intLib.ARITH_TAC)
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_abs_member:
  bounded_int_fraction_abs fraction = fraction \/
  bounded_int_fraction_abs fraction =
    bounded_int_fraction_neg fraction
Proof
  rw [bounded_int_fraction_abs_def,
      compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def]
QED

Theorem bounded_int_fraction_interval_abs_upper_member:
  bounded_int_fraction_interval_abs_upper (lower,upper) = lower \/
  bounded_int_fraction_interval_abs_upper (lower,upper) =
    bounded_int_fraction_neg lower \/
  bounded_int_fraction_interval_abs_upper (lower,upper) = upper \/
  bounded_int_fraction_interval_abs_upper (lower,upper) =
    bounded_int_fraction_neg upper
Proof
  rw [bounded_int_fraction_interval_abs_upper_def,
      bounded_int_fraction_abs_def,
      compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def]
QED

Theorem bounded_interval64_abs_upper_covers_object_q:
  bounded_interval64_covers_object_q interval object_interval ==>
  bounded_word64_upper_covers_object_q
    (bounded_interval64_abs_upper interval)
    (bounded_object_q_interval_abs_upper_cv object_interval)
Proof
  rw [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> every_case_tac
  >> gvs []
  >> PairCases_on `x`
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_covers_object_q_ints_contains_endpoints
  >> `bounded_object_q_ints
        (bounded_object_q_interval_abs_upper_cv object_interval) =
      SOME
        (bounded_int_fraction_interval_abs_upper
          ((x0,x1),(x2,x3)))` by
       (irule bounded_object_q_interval_abs_upper_cv_decodes
        >> simp [])
  >> rw [bounded_word64_upper_covers_object_q_def]
  >> gvs []
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def]
  >> imp_res_tac bounded_interval64_abs_upper_fraction_bounds
  >> rw [bounded_int_fraction_interval_abs_upper_def,
         bounded_int_fraction_abs_def,
         bounded_int_fraction_neg_def,
         bounded_word64_upper_covers_int_fraction_def,
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_word64_product128_upper_covers_int_fraction:
  bounded_word64_upper_covers_int_fraction left
      (left_numerator,left_denominator) /\
  bounded_word64_upper_covers_int_fraction right
      (right_numerator,right_denominator) /\
  0 <= left_numerator /\ 0 <= right_numerator ==>
  bounded128_upper_covers_int_fraction
    (bounded_word64_product128 left right)
    (bounded_int_fraction_mul
      (left_numerator,left_denominator)
      (right_numerator,right_denominator))
Proof
  rw [bounded_word64_upper_covers_int_fraction_def,
      bounded128_upper_covers_int_fraction_def,
      compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def,
      compute_boundedTaylorCompleteTheory.bounded_word64_product128_value]
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> simp [])
  >> `0 <= left_denominator * &(w2n left)` by
       (irule integerTheory.INT_LE_MUL >> simp [] >> intLib.ARITH_TAC)
  >> `0 <= (&1099511627776:int) * right_numerator` by
       (irule integerTheory.INT_LE_MUL >> simp [])
  >> `0 <= right_denominator * &(w2n right)` by
       (irule integerTheory.INT_LE_MUL >> simp [] >> intLib.ARITH_TAC)
  >> `((&1099511627776:int) * left_numerator) *
        ((&1099511627776:int) * right_numerator) <=
      (left_denominator * &(w2n left)) *
        ((&1099511627776:int) * right_numerator)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_right_mono_nonnegative
        >> simp [])
  >> `(left_denominator * &(w2n left)) *
        ((&1099511627776:int) * right_numerator) <=
      (left_denominator * &(w2n left)) *
        (right_denominator * &(w2n right))` by
        (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> PURE_REWRITE_TAC
       [GSYM integerTheory.INT_OF_NUM_MUL]
  >> intLib.ARITH_TAC
QED

Theorem bounded_word64_product128_upper_covers_object_q:
  bounded_word64_upper_covers_object_q left left_object /\
  bounded_word64_upper_covers_object_q right right_object /\
  bounded_object_q_nonnegative left_object /\
  bounded_object_q_nonnegative right_object ==>
  bounded128_upper_covers_object_q
    (bounded_word64_product128 left right)
    (bounded_object_q_mul_cv left_object right_object)
Proof
  rw [bounded_word64_upper_covers_object_q_def,
      bounded_object_q_nonnegative_def,
      bounded128_upper_covers_object_q_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes
  >> gvs []
  >> irule bounded_word64_product128_upper_covers_int_fraction
  >> simp []
QED

val _ = export_theory ();
