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

Definition bounded_word64_object_q_cv_def:
  bounded_word64_object_q_cv (magnitude:word64) =
    Pair
      (Pair (Num (w2n magnitude)) (Num 0))
      (Num 1099511627775)
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

Definition bounded192_upper_covers_int_fraction_def:
  bounded192_upper_covers_int_fraction magnitude
      ((numerator,denominator):int # int) <=>
    0 < denominator /\
    (&1329227995784915872903807060280344576:int) * numerator <=
      denominator * &(bounded192_to_num magnitude)
End

Definition bounded192_upper_covers_object_q_def:
  bounded192_upper_covers_object_q magnitude encoded <=>
    case bounded_object_q_ints encoded of
    | NONE => F
    | SOME fraction =>
        bounded192_upper_covers_int_fraction magnitude fraction
End

Definition bounded_object_q_dot_abs_upper_acc_cv_def:
  bounded_object_q_dot_abs_upper_acc_cv [] [] accumulator = accumulator /\
  bounded_object_q_dot_abs_upper_acc_cv [] (_::_) accumulator = Num 0 /\
  bounded_object_q_dot_abs_upper_acc_cv (_::_) [] accumulator = Num 0 /\
  bounded_object_q_dot_abs_upper_acc_cv
      (radius::radii) (entry::entries) accumulator =
    bounded_object_q_dot_abs_upper_acc_cv radii entries
      (bounded_object_q_add_cv accumulator
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv radius)
          (bounded_object_q_interval_abs_upper_cv entry)))
End

Definition bounded_object_q_quadratic_contribution_cv_def:
  bounded_object_q_quadratic_contribution_cv
      (left_radius:word64) (right_radius:word64) double entry =
    let raw =
      bounded_object_q_mul_cv
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv left_radius)
          (bounded_word64_object_q_cv right_radius))
        (bounded_object_q_interval_abs_upper_cv entry)
    in
      if double then bounded_object_q_add_cv raw raw else raw
End

Definition bounded_object_q_quadratic_abs_upper_acc_cv_def:
  bounded_object_q_quadratic_abs_upper_acc_cv [] [] accumulator =
      accumulator /\
  bounded_object_q_quadratic_abs_upper_acc_cv [] (_::_) accumulator =
      Num 0 /\
  bounded_object_q_quadratic_abs_upper_acc_cv (_::_) [] accumulator =
      Num 0 /\
  bounded_object_q_quadratic_abs_upper_acc_cv
      ((left_radius,right_radius,double)::weights)
      (entry::entries) accumulator =
    bounded_object_q_quadratic_abs_upper_acc_cv weights entries
      (bounded_object_q_add_cv accumulator
        (bounded_object_q_quadratic_contribution_cv
          left_radius right_radius double entry))
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

Theorem bounded_word64_object_q_cv_decodes:
  bounded_object_q_ints (bounded_word64_object_q_cv magnitude) =
    SOME (&(w2n magnitude),&1099511627776)
Proof
  simp [bounded_word64_object_q_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
QED

Theorem bounded_word64_object_q_cv_nonnegative:
  bounded_object_q_nonnegative
    (bounded_word64_object_q_cv magnitude)
Proof
  simp [bounded_object_q_nonnegative_def,
        bounded_word64_object_q_cv_decodes]
QED

Theorem bounded_word64_object_q_cv_exact:
  bounded_word64_upper_covers_object_q magnitude
    (bounded_word64_object_q_cv magnitude)
Proof
  simp [bounded_word64_upper_covers_object_q_def,
        bounded_word64_upper_covers_int_fraction_def,
        bounded_word64_object_q_cv_decodes]
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

Theorem bounded_int_fraction_abs_nonnegative:
  0 < denominator ==>
  0 < SND (bounded_int_fraction_abs (numerator,denominator)) /\
  0 <= FST (bounded_int_fraction_abs (numerator,denominator))
Proof
  rw [bounded_int_fraction_abs_def,
      bounded_int_fraction_neg_def,
      compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def,
      compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> fs [integerTheory.INT_MUL_COMM, integerTheory.INT_LE_MONO]
  >> intLib.ARITH_TAC
QED

Theorem bounded_int_fraction_interval_abs_upper_nonnegative:
  0 < SND lower /\ 0 < SND upper ==>
  0 < SND (bounded_int_fraction_interval_abs_upper (lower,upper)) /\
  0 <= FST (bounded_int_fraction_interval_abs_upper (lower,upper))
Proof
  PairCases_on `lower`
  >> PairCases_on `upper`
  >> strip_tac
  >> assume_tac
       (Q.INST [`numerator` |-> `lower0`, `denominator` |-> `lower1`]
          bounded_int_fraction_abs_nonnegative)
  >> assume_tac
       (Q.INST [`numerator` |-> `upper0`, `denominator` |-> `upper1`]
          bounded_int_fraction_abs_nonnegative)
  >> fs []
  >> rw [bounded_int_fraction_interval_abs_upper_def,
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_max_def]
  >> fs []
QED

Theorem bounded_object_q_interval_abs_upper_cv_nonnegative:
  bounded_object_q_interval_ints object_interval =
    SOME (lower,upper) ==>
  bounded_object_q_nonnegative
    (bounded_object_q_interval_abs_upper_cv object_interval)
Proof
  strip_tac
  >> PairCases_on `lower`
  >> PairCases_on `upper`
  >> `bounded_object_q_ints
        (bounded_object_q_interval_abs_upper_cv object_interval) =
      SOME
        (bounded_int_fraction_interval_abs_upper
          ((lower0,lower1),(upper0,upper1)))` by
       (irule bounded_object_q_interval_abs_upper_cv_decodes
        >> simp [])
  >> rw [bounded_object_q_nonnegative_def]
  >> gvs []
  >> Cases_on `object_interval`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive
  >> assume_tac
       (Q.INST
         [`lower` |-> `(lower0,lower1)`,
          `upper` |-> `(upper0,upper1)`]
         bounded_int_fraction_interval_abs_upper_nonnegative)
  >> gvs []
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

Theorem bounded128_add_upper_covers_int_fraction:
  bounded128_upper_covers_int_fraction left
      (left_numerator,left_denominator) /\
  bounded128_upper_covers_int_fraction right
      (right_numerator,right_denominator) /\
  bounded128_add_words left right = SOME result ==>
  bounded128_upper_covers_int_fraction result
    (bounded_int_fraction_add
      (left_numerator,left_denominator)
      (right_numerator,right_denominator))
Proof
  rw [bounded128_upper_covers_int_fraction_def,
      compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_add_def]
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> simp [])
  >> fs [compute_boundedTheory.bounded128_add_words_refines]
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> gvs []
  >> PURE_REWRITE_TAC [GSYM integerTheory.INT_ADD]
  >> irule
       compute_boundedAnalyticObjectRefinementTheory.bounded_int_fraction_add_upper_bound
  >> simp []
QED

Theorem bounded128_add_upper_covers_object_q:
  bounded128_upper_covers_object_q left left_object /\
  bounded128_upper_covers_object_q right right_object /\
  bounded128_add_words left right = SOME result ==>
  bounded128_upper_covers_object_q result
    (bounded_object_q_add_cv left_object right_object)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints left_object`
  >> fs [bounded128_upper_covers_object_q_def]
  >> PairCases_on `x`
  >> Cases_on `bounded_object_q_ints right_object`
  >> fs [bounded128_upper_covers_object_q_def]
  >> PairCases_on `x`
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv left_object right_object) =
      SOME (x0 * x1' + x0' * x1,x1 * x1')` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> rw [bounded128_upper_covers_object_q_def]
  >> gvs []
  >> irule
       (SIMP_RULE (srw_ss())
         [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_add_def]
         bounded128_add_upper_covers_int_fraction)
  >> qexists_tac `left`
  >> qexists_tac `right`
  >> simp []
QED

Theorem bounded128_word64_product192_upper_covers_int_fraction:
  bounded128_upper_covers_int_fraction left
      (left_numerator,left_denominator) /\
  bounded_word64_upper_covers_int_fraction right
      (right_numerator,right_denominator) /\
  0 <= left_numerator /\ 0 <= right_numerator /\
  bounded128_mul_word64_to_192_words left right = SOME result ==>
  bounded192_upper_covers_int_fraction result
    (bounded_int_fraction_mul
      (left_numerator,left_denominator)
      (right_numerator,right_denominator))
Proof
  rw [bounded128_upper_covers_int_fraction_def,
      bounded_word64_upper_covers_int_fraction_def,
      bounded192_upper_covers_int_fraction_def,
      compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> simp [])
  >> imp_res_tac
       compute_boundedWideTheory.bounded128_mul_word64_to_192_words_some
  >> gvs []
  >> `0 <= left_denominator * &(bounded128_to_num left)` by
       (irule integerTheory.INT_LE_MUL >> simp [] >> intLib.ARITH_TAC)
  >> `0 <= (&1099511627776:int) * right_numerator` by
       (irule integerTheory.INT_LE_MUL >> simp [])
  >> `0 <= right_denominator * &(w2n right)` by
       (irule integerTheory.INT_LE_MUL >> simp [] >> intLib.ARITH_TAC)
  >> `((&1208925819614629174706176:int) * left_numerator) *
        ((&1099511627776:int) * right_numerator) <=
      (left_denominator * &(bounded128_to_num left)) *
        ((&1099511627776:int) * right_numerator)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_right_mono_nonnegative
        >> simp [])
  >> `(left_denominator * &(bounded128_to_num left)) *
        ((&1099511627776:int) * right_numerator) <=
      (left_denominator * &(bounded128_to_num left)) *
        (right_denominator * &(w2n right))` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> PURE_REWRITE_TAC [GSYM integerTheory.INT_OF_NUM_MUL]
  >> intLib.ARITH_TAC
QED

Theorem bounded192_add_upper_covers_int_fraction:
  bounded192_upper_covers_int_fraction left
      (left_numerator,left_denominator) /\
  bounded192_upper_covers_int_fraction right
      (right_numerator,right_denominator) /\
  bounded192_add_words left right = SOME result ==>
  bounded192_upper_covers_int_fraction result
    (bounded_int_fraction_add
      (left_numerator,left_denominator)
      (right_numerator,right_denominator))
Proof
  rw [bounded192_upper_covers_int_fraction_def,
      compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_add_def]
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> simp [])
  >> fs [compute_boundedTheory.bounded192_add_words_refines]
  >> imp_res_tac compute_boundedTheory.bounded192_add_some
  >> gvs []
  >> PURE_REWRITE_TAC [GSYM integerTheory.INT_ADD]
  >> irule
       compute_boundedAnalyticObjectRefinementTheory.bounded_int_fraction_add_upper_bound
  >> simp []
QED

Theorem bounded_object_q_mul_cv_nonnegative:
  bounded_object_q_nonnegative left_object /\
  bounded_object_q_nonnegative right_object ==>
  bounded_object_q_nonnegative
    (bounded_object_q_mul_cv left_object right_object)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints left_object`
  >> fs [bounded_object_q_nonnegative_def]
  >> PairCases_on `x`
  >> Cases_on `bounded_object_q_ints right_object`
  >> fs [bounded_object_q_nonnegative_def]
  >> PairCases_on `x`
  >> `bounded_object_q_ints
        (bounded_object_q_mul_cv left_object right_object) =
      SOME (bounded_int_fraction_mul (x0,x1) (x0',x1'))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes
        >> simp [])
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
  >> irule
       (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
  >> simp []
QED

Theorem bounded128_word64_product192_upper_covers_object_q:
  bounded128_upper_covers_object_q left left_object /\
  bounded_word64_upper_covers_object_q right right_object /\
  bounded_object_q_nonnegative left_object /\
  bounded_object_q_nonnegative right_object /\
  bounded128_mul_word64_to_192_words left right = SOME result ==>
  bounded192_upper_covers_object_q result
    (bounded_object_q_mul_cv left_object right_object)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints left_object`
  >> fs [bounded128_upper_covers_object_q_def,
         bounded_object_q_nonnegative_def]
  >> PairCases_on `x`
  >> Cases_on `bounded_object_q_ints right_object`
  >> fs [bounded_word64_upper_covers_object_q_def,
         bounded_object_q_nonnegative_def]
  >> PairCases_on `x`
  >> `bounded_object_q_ints
        (bounded_object_q_mul_cv left_object right_object) =
      SOME (bounded_int_fraction_mul (x0,x1) (x0',x1'))` by
       (irule
          compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_mul_cv_decodes
        >> simp [])
  >> rw [bounded192_upper_covers_object_q_def]
  >> gvs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
  >> match_mp_tac
       (Q.INST
         [`left` |-> `left`, `right` |-> `right`, `result` |-> `result`,
          `left_numerator` |-> `x0`, `left_denominator` |-> `x1`,
          `right_numerator` |-> `x0'`, `right_denominator` |-> `x1'`]
         (SIMP_RULE (srw_ss())
           [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_mul_def]
           bounded128_word64_product192_upper_covers_int_fraction))
  >> simp []
QED

Theorem bounded192_add_upper_covers_object_q:
  bounded192_upper_covers_object_q left left_object /\
  bounded192_upper_covers_object_q right right_object /\
  bounded192_add_words left right = SOME result ==>
  bounded192_upper_covers_object_q result
    (bounded_object_q_add_cv left_object right_object)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints left_object`
  >> fs [bounded192_upper_covers_object_q_def]
  >> PairCases_on `x`
  >> Cases_on `bounded_object_q_ints right_object`
  >> fs [bounded192_upper_covers_object_q_def]
  >> PairCases_on `x`
  >> `bounded_object_q_ints
        (bounded_object_q_add_cv left_object right_object) =
      SOME (x0 * x1' + x0' * x1,x1 * x1')` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> rw [bounded192_upper_covers_object_q_def]
  >> gvs []
  >> match_mp_tac
       (Q.INST
         [`left` |-> `left`, `right` |-> `right`, `result` |-> `result`,
          `left_numerator` |-> `x0`, `left_denominator` |-> `x1`,
          `right_numerator` |-> `x0'`, `right_denominator` |-> `x1'`]
         (SIMP_RULE (srw_ss())
           [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_add_def]
           bounded192_add_upper_covers_int_fraction))
  >> simp []
QED

Theorem bounded_quadratic_abs_contribution_covers_object_q:
  bounded_interval64_covers_object_q entry object_entry /\
  bounded128_mul_word64_to_192_words
      (bounded_word64_product128 left_radius right_radius)
      (bounded_interval64_abs_upper entry) = SOME raw /\
  (if double then bounded192_add_words raw raw else SOME raw) =
    SOME contribution ==>
  bounded192_upper_covers_object_q contribution
    (bounded_object_q_quadratic_contribution_cv
      left_radius right_radius double object_entry)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_interval_ints object_entry`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> PairCases_on `x`
  >> `bounded_object_q_nonnegative
        (bounded_object_q_interval_abs_upper_cv object_entry)` by
       (irule bounded_object_q_interval_abs_upper_cv_nonnegative
        >> simp [])
  >> `bounded_interval64_covers_object_q entry object_entry` by
       (rw
          [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
        >> simp [])
  >> `bounded_word64_upper_covers_object_q
        (bounded_interval64_abs_upper entry)
        (bounded_object_q_interval_abs_upper_cv object_entry)` by
       metis_tac [bounded_interval64_abs_upper_covers_object_q]
  >> `bounded128_upper_covers_object_q
        (bounded_word64_product128 left_radius right_radius)
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv left_radius)
          (bounded_word64_object_q_cv right_radius))` by
       (irule bounded_word64_product128_upper_covers_object_q
        >> simp [bounded_word64_object_q_cv_exact,
                 bounded_word64_object_q_cv_nonnegative])
  >> `bounded_object_q_nonnegative
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv left_radius)
          (bounded_word64_object_q_cv right_radius))` by
       (irule bounded_object_q_mul_cv_nonnegative
        >> simp [bounded_word64_object_q_cv_nonnegative])
  >> `bounded192_upper_covers_object_q raw
        (bounded_object_q_mul_cv
          (bounded_object_q_mul_cv
            (bounded_word64_object_q_cv left_radius)
            (bounded_word64_object_q_cv right_radius))
          (bounded_object_q_interval_abs_upper_cv object_entry))` by
       (match_mp_tac
          (Q.INST
            [`left` |->
               `bounded_word64_product128 left_radius right_radius`,
             `right` |-> `bounded_interval64_abs_upper entry`,
             `result` |-> `raw`,
             `left_object` |->
               `bounded_object_q_mul_cv
                  (bounded_word64_object_q_cv left_radius)
                  (bounded_word64_object_q_cv right_radius)`,
             `right_object` |->
               `bounded_object_q_interval_abs_upper_cv object_entry`]
            bounded128_word64_product192_upper_covers_object_q)
        >> simp [])
  >> Cases_on `double`
  >> gvs [bounded_object_q_quadratic_contribution_cv_def, LET_THM]
  >> match_mp_tac
       (Q.INST
         [`left` |-> `raw`, `right` |-> `raw`,
          `result` |-> `contribution`,
          `left_object` |->
            `bounded_object_q_mul_cv
              (bounded_object_q_mul_cv
                (bounded_word64_object_q_cv left_radius)
                (bounded_word64_object_q_cv right_radius))
              (bounded_object_q_interval_abs_upper_cv object_entry)`,
          `right_object` |->
            `bounded_object_q_mul_cv
              (bounded_object_q_mul_cv
                (bounded_word64_object_q_cv left_radius)
                (bounded_word64_object_q_cv right_radius))
              (bounded_object_q_interval_abs_upper_cv object_entry)`]
         bounded192_add_upper_covers_object_q)
  >> simp []
QED

Theorem bounded_quadratic_abs_upper_acc_covers_object_q:
  !weights entries object_entries accumulator object_accumulator result.
    LIST_REL bounded_interval64_covers_object_q
      entries object_entries /\
    bounded192_upper_covers_object_q accumulator object_accumulator /\
    bounded_quadratic_abs_upper_acc weights entries accumulator =
      SOME result ==>
    bounded192_upper_covers_object_q result
      (bounded_object_q_quadratic_abs_upper_acc_cv
        weights object_entries object_accumulator)
Proof
  Induct
  >- (Cases_on `entries`
      >> Cases_on `object_entries`
      >> gvs
           [compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def,
            bounded_object_q_quadratic_abs_upper_acc_cv_def, LIST_REL_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >- gvs
       [compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def,
        LIST_REL_def]
  >> Cases_on `object_entries`
  >- gvs [LIST_REL_def]
  >> rpt gen_tac
  >> strip_tac
  >> fs [LIST_REL_def]
  >> fs
       [compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def,
        bounded_object_q_quadratic_abs_upper_acc_cv_def, LET_THM]
  >> Cases_on
       `bounded128_mul_word64_to_192_words
          (bounded_word64_product128 h0 h1)
          (bounded_interval64_abs_upper h)`
  >> fs []
  >> Cases_on
       `if h2 then bounded192_add_words x x else SOME x`
  >> fs []
  >> Cases_on `bounded192_add_words accumulator x'`
  >> fs []
  >> `bounded192_upper_covers_object_q x'
        (bounded_object_q_quadratic_contribution_cv h0 h1 h2 h')` by
       (match_mp_tac
          (Q.INST
            [`left_radius` |-> `h0`, `right_radius` |-> `h1`,
             `double` |-> `h2`, `entry` |-> `h`,
             `object_entry` |-> `h'`, `raw` |-> `x`,
             `contribution` |-> `x'`]
            bounded_quadratic_abs_contribution_covers_object_q)
        >> simp [])
  >> `bounded192_upper_covers_object_q x''
        (bounded_object_q_add_cv object_accumulator
          (bounded_object_q_quadratic_contribution_cv h0 h1 h2 h'))` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `accumulator`, `right` |-> `x'`,
             `result` |-> `x''`,
             `left_object` |-> `object_accumulator`,
             `right_object` |->
               `bounded_object_q_quadratic_contribution_cv h0 h1 h2 h'`]
            bounded192_add_upper_covers_object_q)
        >> simp [])
  >> qpat_x_assum
       `!entries object_entries accumulator object_accumulator result. _`
       (match_mp_tac o Q.SPECL
         [`t`, `t'`, `x''`,
          `bounded_object_q_add_cv object_accumulator
            (bounded_object_q_quadratic_contribution_cv h0 h1 h2 h')`,
          `result`])
  >> simp []
QED

Theorem bounded_dot_abs_upper_acc_covers_object_q:
  !radii entries object_entries accumulator object_accumulator result.
    LIST_REL bounded_interval64_covers_object_q
      entries object_entries /\
    bounded128_upper_covers_object_q accumulator object_accumulator /\
    bounded_dot_abs_upper_acc radii entries accumulator = SOME result ==>
    bounded128_upper_covers_object_q result
      (bounded_object_q_dot_abs_upper_acc_cv
        radii object_entries object_accumulator)
Proof
  Induct
  >- (Cases_on `entries`
      >> Cases_on `object_entries`
      >> gvs
           [compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def,
            bounded_object_q_dot_abs_upper_acc_cv_def, LIST_REL_def])
  >> Cases_on `entries`
  >- gvs
       [compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def,
        LIST_REL_def]
  >> Cases_on `object_entries`
  >- gvs [LIST_REL_def]
  >> rpt gen_tac
  >> strip_tac
  >> fs [LIST_REL_def]
  >> Cases_on `bounded_object_q_interval_ints h'`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> PairCases_on `x`
  >> fs
       [compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def,
        bounded_object_q_dot_abs_upper_acc_cv_def, LET_THM]
  >> Cases_on
       `bounded128_add_words accumulator
          (bounded_word64_product128 h''
            (bounded_interval64_abs_upper h))`
  >> fs []
  >> `bounded_object_q_nonnegative
        (bounded_object_q_interval_abs_upper_cv h')` by
       (irule bounded_object_q_interval_abs_upper_cv_nonnegative
        >> simp [])
  >> `bounded_interval64_covers_object_q h h'` by
       (rw
          [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
        >> simp [])
  >> `bounded_word64_upper_covers_object_q
        (bounded_interval64_abs_upper h)
        (bounded_object_q_interval_abs_upper_cv h')` by
       metis_tac [bounded_interval64_abs_upper_covers_object_q]
  >> `bounded128_upper_covers_object_q
        (bounded_word64_product128 h''
          (bounded_interval64_abs_upper h))
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv h'')
          (bounded_object_q_interval_abs_upper_cv h'))` by
       (irule bounded_word64_product128_upper_covers_object_q
        >> simp [bounded_word64_object_q_cv_exact,
                 bounded_word64_object_q_cv_nonnegative])
  >> `bounded128_upper_covers_object_q x
        (bounded_object_q_add_cv object_accumulator
          (bounded_object_q_mul_cv
            (bounded_word64_object_q_cv h'')
            (bounded_object_q_interval_abs_upper_cv h')))` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `accumulator`,
             `right` |->
               `bounded_word64_product128 h''
                  (bounded_interval64_abs_upper h)`,
             `result` |-> `x`,
             `left_object` |-> `object_accumulator`,
             `right_object` |->
               `bounded_object_q_mul_cv
                  (bounded_word64_object_q_cv h'')
                  (bounded_object_q_interval_abs_upper_cv h')`]
            bounded128_add_upper_covers_object_q)
        >> simp [])
  >> qpat_x_assum
       `!entries object_entries accumulator object_accumulator result. _`
       (match_mp_tac o Q.SPECL
         [`t`, `t'`, `x`,
          `bounded_object_q_add_cv object_accumulator
            (bounded_object_q_mul_cv
              (bounded_word64_object_q_cv h'')
              (bounded_object_q_interval_abs_upper_cv h'))`,
          `result`])
  >> simp []
QED

Theorem bounded128_zero_covers_object_q_zero:
  bounded128_upper_covers_object_q (Bounded128 0w 0w)
    (bounded_word64_object_q_cv 0w)
Proof
  simp [bounded128_upper_covers_object_q_def,
        bounded128_upper_covers_int_fraction_def,
        bounded_word64_object_q_cv_decodes,
        compute_boundedTheory.bounded128_to_num_def]
QED

Theorem bounded192_zero_covers_object_q_zero:
  bounded192_upper_covers_object_q bounded192_zero
    (bounded_word64_object_q_cv 0w)
Proof
  simp [bounded192_upper_covers_object_q_def,
        bounded192_upper_covers_int_fraction_def,
        bounded_word64_object_q_cv_decodes,
        compute_boundedWideTheory.bounded192_zero_def,
        compute_boundedTheory.bounded192_to_num_def]
QED

Theorem bounded_dot_abs_upper_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
      entries object_entries /\
  bounded_dot_abs_upper radii entries = SOME result ==>
  bounded128_upper_covers_object_q result
    (bounded_object_q_dot_abs_upper_acc_cv radii object_entries
      (bounded_word64_object_q_cv 0w))
Proof
  rw [compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_def]
  >> match_mp_tac
       (Q.SPECL
         [`radii`, `entries`, `object_entries`, `Bounded128 0w 0w`,
          `bounded_word64_object_q_cv 0w`, `result`]
         bounded_dot_abs_upper_acc_covers_object_q)
  >> simp [bounded128_zero_covers_object_q_zero]
QED

Theorem bounded_quadratic_abs_upper_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
      hessian object_hessian /\
  bounded_quadratic_abs_upper radii hessian = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded192_upper_covers_object_q result
      (bounded_object_q_quadratic_abs_upper_acc_cv
        weights object_hessian (bounded_word64_object_q_cv 0w))
Proof
  rw [compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_def]
  >> every_case_tac
  >> gvs []
  >> match_mp_tac
       (Q.SPECL
         [`x`, `hessian`, `object_hessian`, `bounded192_zero`,
          `bounded_word64_object_q_cv 0w`, `result`]
         bounded_quadratic_abs_upper_acc_covers_object_q)
  >> simp [bounded192_zero_covers_object_q_zero]
QED

Theorem bounded_completion_scale41_num_identity:
  high < 18446744073709551616 /\
  low < 18446744073709551616 ==>
  340282366920938463463374607431768211456 *
      (high DIV 8388608) +
    ((2199023255552 * low) MOD 18446744073709551616 +
     18446744073709551616 *
       (((2199023255552 * high) MOD 18446744073709551616 +
         low DIV 8388608) MOD 18446744073709551616)) =
  2199023255552 *
    (18446744073709551616 * high + low)
Proof
  strip_tac
  >> qabbrev_tac `high_q = high DIV 8388608`
  >> qabbrev_tac `high_r = high MOD 8388608`
  >> qabbrev_tac `low_q = low DIV 8388608`
  >> qabbrev_tac `low_r = low MOD 8388608`
  >> `high_r < 8388608 /\ low_r < 8388608` by
       (qunabbrev_tac `high_r`
        >> qunabbrev_tac `low_r`
        >> simp [])
  >> `high_q < 2199023255552 /\ low_q < 2199023255552` by
       (qunabbrev_tac `high_q`
        >> qunabbrev_tac `low_q`
        >> simp [DIV_LT_X])
  >> `high_r + 8388608 * high_q = high /\
      low_r + 8388608 * low_q = low` by
       (conj_tac
        >> qunabbrev_tac `high_r`
        >> qunabbrev_tac `high_q`
        >> qunabbrev_tac `low_r`
        >> qunabbrev_tac `low_q`
        >> irule compute_boundedTheory.bounded_division_reconstruct
        >> simp [])
  >> `2199023255552 * high =
        high_q * 18446744073709551616 +
          2199023255552 * high_r /\
      2199023255552 * low =
        low_q * 18446744073709551616 +
          2199023255552 * low_r` by intLib.ARITH_TAC
  >> `2199023255552 * high_r < 18446744073709551616 /\
      2199023255552 * low_r < 18446744073709551616 /\
      2199023255552 * high_r + low_q < 18446744073709551616` by
       intLib.ARITH_TAC
  >> `(2199023255552 * high) MOD 18446744073709551616 =
        2199023255552 * high_r` by
       (qpat_x_assum `2199023255552 * high = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `high_q`
        >> simp [])
  >> `(2199023255552 * low) MOD 18446744073709551616 =
        2199023255552 * low_r` by
       (qpat_x_assum `2199023255552 * low = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `low_q`
        >> simp [])
  >> asm_rewrite_tac []
  >> simp [LESS_MOD]
  >> intLib.ARITH_TAC
QED

Theorem bounded_completion_scale41_value:
  bounded192_to_num (bounded128_scale41 value) =
    2199023255552 * bounded128_to_num value
Proof
  Cases_on `value`
  >> rename1 `Bounded128 high low`
  >> Cases_on `high`
  >> Cases_on `low`
  >> simp [compute_boundedWideSignedTheory.bounded128_scale41_def,
           compute_boundedTheory.bounded128_to_num_def,
           compute_boundedTheory.bounded192_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           w2n_lsr, word_lsl_n2w, word_add_n2w, dimword_64]
  >> fs [dimword_64]
  >> `((n2w n'):word64) >>> 23 = n2w (n' DIV 8388608)` by
       (mp_tac
          (Q.SPECL [`n'`, `23`]
            (n2w_DIV |> INST_TYPE [alpha |-> ``:64``]))
        >> simp [dimword_64])
  >> asm_rewrite_tac []
  >> simp [word_add_n2w, dimword_64]
  >> assume_tac
       (Q.INST [`high` |-> `n`, `low` |-> `n'`]
          bounded_completion_scale41_num_identity)
  >> fs []
QED

Definition bounded_object_q_taylor_error_cv_def:
  bounded_object_q_taylor_error_cv radii center_gradient weights hessian =
    let linear =
      bounded_object_q_dot_abs_upper_acc_cv radii center_gradient
        (bounded_word64_object_q_cv 0w) in
    let quadratic =
      bounded_object_q_quadratic_abs_upper_acc_cv weights hessian
        (bounded_word64_object_q_cv 0w) in
      bounded_object_q_add_cv
        (bounded_object_q_add_cv linear linear) quadratic
End

Theorem bounded128_scale41_upper_covers_int_fraction_double:
  bounded128_upper_covers_int_fraction source
      (numerator,denominator) ==>
  bounded192_upper_covers_int_fraction (bounded128_scale41 source)
    (bounded_int_fraction_add
      (numerator,denominator) (numerator,denominator))
Proof
  rw [bounded128_upper_covers_int_fraction_def,
      bounded192_upper_covers_int_fraction_def,
      compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_add_def,
      bounded_completion_scale41_value]
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> simp [])
  >> `((&2199023255552:int) * denominator) *
        ((&1208925819614629174706176:int) * numerator) <=
      ((&2199023255552:int) * denominator) *
        (denominator * &(bounded128_to_num source))` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> PURE_REWRITE_TAC [GSYM integerTheory.INT_OF_NUM_MUL]
  >> intLib.ARITH_TAC
QED

Theorem bounded128_scale41_upper_covers_object_q_double:
  bounded128_upper_covers_object_q source object ==>
  bounded192_upper_covers_object_q (bounded128_scale41 source)
    (bounded_object_q_add_cv object object)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints object`
  >> fs [bounded128_upper_covers_object_q_def]
  >> PairCases_on `x`
  >> `bounded_object_q_ints (bounded_object_q_add_cv object object) =
      SOME (x0 * x1 + x0 * x1,x1 * x1)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_add_cv_decodes
        >> simp [])
  >> rw [bounded192_upper_covers_object_q_def]
  >> gvs []
  >> match_mp_tac
       (Q.INST
         [`source` |-> `source`, `numerator` |-> `x0`,
          `denominator` |-> `x1`]
         (SIMP_RULE (srw_ss())
           [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_add_def]
           bounded128_scale41_upper_covers_int_fraction_double))
  >> simp []
QED

Theorem bounded_taylor_error_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
      center_gradient object_center_gradient /\
  LIST_REL bounded_interval64_covers_object_q
      hessian object_hessian /\
  bounded_taylor_error radii center_gradient hessian = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded192_upper_covers_object_q result
      (bounded_object_q_taylor_error_cv
        radii object_center_gradient weights object_hessian)
Proof
  rw [compute_boundedTaylorCompleteTheory.bounded_taylor_error_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded192_add_words (bounded128_scale41 linear) quadratic =
          SOME result`
  >> `bounded128_upper_covers_object_q linear
        (bounded_object_q_dot_abs_upper_acc_cv radii
          object_center_gradient (bounded_word64_object_q_cv 0w))` by
       (match_mp_tac
          (Q.INST
            [`entries` |-> `center_gradient`,
             `object_entries` |-> `object_center_gradient`,
             `radii` |-> `radii`, `result` |-> `linear`]
            bounded_dot_abs_upper_covers_object_q)
        >> simp [])
  >> mp_tac
       (Q.INST
         [`hessian` |-> `hessian`,
          `object_hessian` |-> `object_hessian`,
          `radii` |-> `radii`, `result` |-> `quadratic`]
         bounded_quadratic_abs_upper_covers_object_q)
  >> impl_tac
  >- simp []
  >> disch_then (qx_choose_then `weights` strip_assume_tac)
  >> qexists_tac `weights`
  >> simp [bounded_object_q_taylor_error_cv_def, LET_THM]
  >> match_mp_tac
       (Q.INST
         [`left` |-> `bounded128_scale41 linear`,
          `right` |-> `quadratic`,
          `result` |-> `result`,
          `left_object` |->
            `bounded_object_q_add_cv
              (bounded_object_q_dot_abs_upper_acc_cv radii
                object_center_gradient (bounded_word64_object_q_cv 0w))
              (bounded_object_q_dot_abs_upper_acc_cv radii
                object_center_gradient (bounded_word64_object_q_cv 0w))`,
          `right_object` |->
            `bounded_object_q_quadratic_abs_upper_acc_cv weights
              object_hessian (bounded_word64_object_q_cv 0w)`]
         bounded192_add_upper_covers_object_q)
  >> simp [bounded128_scale41_upper_covers_object_q_double]
QED

val _ = export_theory ();
