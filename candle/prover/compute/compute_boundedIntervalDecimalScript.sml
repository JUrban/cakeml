(*****************************************************************************
 * Directed decimal-scale endpoint products for the fast nonlinear checker.
 *
 * This is deliberately a separate layer from the established scale-2^40
 * interval engine.  Values use the same normalized sign/magnitude carrier,
 * but every theorem below names the 10^12 scale explicitly.  That prevents
 * an accidental representation-only identification of the two arithmetics.
 *****************************************************************************)
Theory compute_boundedIntervalDecimal
Ancestors
  compute_boundedInterval compute_boundedSigned compute_boundedSignedEndpoint
Libs
  bossLib preamble

Definition bounded_scaled_mul_floor64_decimal_def:
  bounded_scaled_mul_floor64_decimal left right =
    case bounded_signed_word64_mul_floor_decimal left right of
    | NONE => NONE
    | SOME wide => bounded_signed128_narrow64 wide
End

Definition bounded_scaled_mul_ceil64_decimal_def:
  bounded_scaled_mul_ceil64_decimal left right =
    case bounded_signed_word64_mul_ceil_decimal left right of
    | NONE => NONE
    | SOME wide => bounded_signed128_narrow64 wide
End

Definition bounded_interval64_product_from_pairs_decimal_def:
  bounded_interval64_product_from_pairs_decimal
      lower_left lower_right upper_left upper_right =
    case bounded_scaled_mul_floor64_decimal lower_left lower_right of
    | NONE => NONE
    | SOME lower =>
        case bounded_scaled_mul_ceil64_decimal upper_left upper_right of
        | NONE => NONE
        | SOME upper => SOME (BoundedInterval64 lower upper)
End

Definition bounded_interval64_product_mixed_decimal_def:
  bounded_interval64_product_mixed_decimal
      left_lower left_upper right_lower right_upper =
    case bounded_scaled_mul_floor64_decimal left_lower right_upper of
    | NONE => NONE
    | SOME lower_left =>
      case bounded_scaled_mul_floor64_decimal left_upper right_lower of
      | NONE => NONE
      | SOME lower_right =>
        case bounded_scaled_mul_ceil64_decimal left_lower right_lower of
        | NONE => NONE
        | SOME upper_left =>
          case bounded_scaled_mul_ceil64_decimal left_upper right_upper of
          | NONE => NONE
          | SOME upper_right =>
              SOME
                (BoundedInterval64
                  (bounded_signed64_min lower_left lower_right)
                  (bounded_signed64_max upper_left upper_right))
End

Definition bounded_interval64_mul_unchecked_decimal_def:
  bounded_interval64_mul_unchecked_decimal
      (BoundedInterval64 left_lower left_upper)
      (BoundedInterval64 right_lower right_upper) =
    if bounded_signed64_nonnegative left_lower then
      if bounded_signed64_nonnegative right_lower then
        bounded_interval64_product_from_pairs_decimal
          left_lower right_lower left_upper right_upper
      else if bounded_signed64_nonpositive right_upper then
        bounded_interval64_product_from_pairs_decimal
          left_upper right_lower left_lower right_upper
      else
        bounded_interval64_product_from_pairs_decimal
          left_upper right_lower left_upper right_upper
    else if bounded_signed64_nonpositive left_upper then
      if bounded_signed64_nonnegative right_lower then
        bounded_interval64_product_from_pairs_decimal
          left_lower right_upper left_upper right_lower
      else if bounded_signed64_nonpositive right_upper then
        bounded_interval64_product_from_pairs_decimal
          left_upper right_upper left_lower right_lower
      else
        bounded_interval64_product_from_pairs_decimal
          left_lower right_upper left_lower right_lower
    else if bounded_signed64_nonnegative right_lower then
      bounded_interval64_product_from_pairs_decimal
        left_lower right_upper left_upper right_upper
    else if bounded_signed64_nonpositive right_upper then
      bounded_interval64_product_from_pairs_decimal
        left_upper right_lower left_lower right_lower
    else
      bounded_interval64_product_mixed_decimal
        left_lower left_upper right_lower right_upper
End

Definition bounded_interval64_mul_decimal_def:
  bounded_interval64_mul_decimal left right =
    if bounded_interval64_valid left /\ bounded_interval64_valid right then
      bounded_interval64_mul_unchecked_decimal left right
    else NONE
End

Theorem bounded_div_floor_decimal_scaled_le:
  (value DIV 1000000000000) * 1000000000000 <= value
Proof
  simp [GSYM arithmeticTheory.X_LE_DIV]
QED

Theorem bounded_div_ceil_decimal:
  (value + 999999999999) DIV 1000000000000 =
    value DIV 1000000000000 +
      if value MOD 1000000000000 = 0 then 0 else 1
Proof
  mp_tac
    (Q.INST [`divisor` |-> `1000000000000`]
      compute_boundedSignedTheory.bounded_div_ceil)
  >> simp []
QED

Theorem bounded_div_ceil_decimal_scaled_ge:
  value <=
    ((value + 999999999999) DIV 1000000000000) * 1000000000000
Proof
  mp_tac (Q.SPEC `1000000000000` arithmeticTheory.DIVISION)
  >> simp []
  >> disch_then (qspec_then `value` strip_assume_tac)
  >> Cases_on `value MOD 1000000000000 = 0`
  >- fs [bounded_div_ceil_decimal]
  >> fs [bounded_div_ceil_decimal, arithmeticTheory.LEFT_ADD_DISTRIB]
  >> qpat_x_assum `value = _` (fn th => once_rewrite_tac [th])
  >> rw [arithmeticTheory.ADD_MONO_LESS_EQ]
  >> irule arithmeticTheory.LESS_IMP_LESS_OR_EQ
  >> irule arithmeticTheory.MOD_LESS
  >> numLib.REDUCE_TAC
QED

Theorem bounded_signed_word64_mul_floor_decimal_to_int:
  bounded_signed_word64_mul_floor_decimal
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ==>
  bounded_signed128_to_int result =
    if left_negative <> right_negative then
      -&((w2n left_word * w2n right_word + 999999999999) DIV
         1000000000000)
    else
      &((w2n left_word * w2n right_word) DIV 1000000000000)
Proof
  strip_tac
  >> imp_res_tac bounded_signed_word64_mul_floor_decimal_magnitude
  >> imp_res_tac bounded_signed_word64_mul_floor_decimal_negative
  >> fs [compute_boundedIntervalTheory.bounded_signed128_to_int_components]
  >> Cases_on `left_negative <> right_negative`
  >> fs []
  >> Cases_on
       `(w2n left_word * w2n right_word + 999999999999) DIV
          1000000000000 = 0`
  >> fs []
QED

Theorem bounded_signed_word64_mul_ceil_decimal_to_int:
  bounded_signed_word64_mul_ceil_decimal
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ==>
  bounded_signed128_to_int result =
    if left_negative <> right_negative then
      -&((w2n left_word * w2n right_word) DIV 1000000000000)
    else
      &((w2n left_word * w2n right_word + 999999999999) DIV
         1000000000000)
Proof
  strip_tac
  >> imp_res_tac bounded_signed_word64_mul_ceil_decimal_magnitude
  >> imp_res_tac bounded_signed_word64_mul_ceil_decimal_negative
  >> fs [compute_boundedIntervalTheory.bounded_signed128_to_int_components]
  >> Cases_on `left_negative <> right_negative`
  >> fs []
  >> Cases_on
       `(w2n left_word * w2n right_word) DIV 1000000000000 = 0`
  >> fs []
QED

Theorem bounded_scaled_mul_floor64_decimal_value:
  bounded_scaled_mul_floor64_decimal
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ==>
  bounded_signed64_to_int result =
    if left_negative <> right_negative then
      -&((w2n left_word * w2n right_word + 999999999999) DIV
         1000000000000)
    else
      &((w2n left_word * w2n right_word) DIV 1000000000000)
Proof
  strip_tac
  >> Cases_on
       `bounded_signed_word64_mul_floor_decimal
          (BoundedSigned64 left_negative left_word)
          (BoundedSigned64 right_negative right_word)`
  >> fs [bounded_scaled_mul_floor64_decimal_def]
  >> imp_res_tac bounded_signed128_narrow64_some
  >> imp_res_tac bounded_signed_word64_mul_floor_decimal_to_int
  >> fs []
QED

Theorem bounded_scaled_mul_ceil64_decimal_value:
  bounded_scaled_mul_ceil64_decimal
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ==>
  bounded_signed64_to_int result =
    if left_negative <> right_negative then
      -&((w2n left_word * w2n right_word) DIV 1000000000000)
    else
      &((w2n left_word * w2n right_word + 999999999999) DIV
         1000000000000)
Proof
  strip_tac
  >> Cases_on
       `bounded_signed_word64_mul_ceil_decimal
          (BoundedSigned64 left_negative left_word)
          (BoundedSigned64 right_negative right_word)`
  >> fs [bounded_scaled_mul_ceil64_decimal_def]
  >> imp_res_tac bounded_signed128_narrow64_some
  >> imp_res_tac bounded_signed_word64_mul_ceil_decimal_to_int
  >> fs []
QED

Theorem bounded_scaled_mul_floor64_decimal_lower_bound:
  bounded_scaled_mul_floor64_decimal
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ==>
  (&1000000000000:int) * bounded_signed64_to_int result <=
    bounded_signed64_to_int (BoundedSigned64 left_negative left_word) *
    bounded_signed64_to_int (BoundedSigned64 right_negative right_word)
Proof
  strip_tac
  >> imp_res_tac bounded_scaled_mul_floor64_decimal_value
  >> assume_tac
       (Q.INST
          [`value` |->
             `w2n (left_word:word64) * w2n (right_word:word64)`]
          bounded_div_floor_decimal_scaled_le)
  >> assume_tac
       (Q.INST
          [`value` |->
             `w2n (left_word:word64) * w2n (right_word:word64)`]
          bounded_div_ceil_decimal_scaled_ge)
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_scaled_mul_ceil64_decimal_upper_bound:
  bounded_scaled_mul_ceil64_decimal
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ==>
  bounded_signed64_to_int (BoundedSigned64 left_negative left_word) *
    bounded_signed64_to_int (BoundedSigned64 right_negative right_word) <=
  (&1000000000000:int) * bounded_signed64_to_int result
Proof
  strip_tac
  >> imp_res_tac bounded_scaled_mul_ceil64_decimal_value
  >> assume_tac
       (Q.INST
          [`value` |->
             `w2n (left_word:word64) * w2n (right_word:word64)`]
          bounded_div_floor_decimal_scaled_le)
  >> assume_tac
       (Q.INST
          [`value` |->
             `w2n (left_word:word64) * w2n (right_word:word64)`]
          bounded_div_ceil_decimal_scaled_ge)
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_scaled_mul_floor64_decimal_lower_bound_general:
  bounded_scaled_mul_floor64_decimal left right = SOME result ==>
  (&1000000000000:int) * bounded_signed64_to_int result <=
    bounded_signed64_to_int left * bounded_signed64_to_int right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> metis_tac [bounded_scaled_mul_floor64_decimal_lower_bound]
QED

Theorem bounded_scaled_mul_ceil64_decimal_upper_bound_general:
  bounded_scaled_mul_ceil64_decimal left right = SOME result ==>
  bounded_signed64_to_int left * bounded_signed64_to_int right <=
    (&1000000000000:int) * bounded_signed64_to_int result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> metis_tac [bounded_scaled_mul_ceil64_decimal_upper_bound]
QED

Theorem bounded_scaled_mul_floor64_decimal_normalized:
  bounded_scaled_mul_floor64_decimal left right = SOME result ==>
  bounded_signed64_normalized result
Proof
  rw [bounded_scaled_mul_floor64_decimal_def]
  >> Cases_on `bounded_signed_word64_mul_floor_decimal left right`
  >> gvs []
  >> imp_res_tac bounded_signed128_narrow64_some
QED

Theorem bounded_scaled_mul_ceil64_decimal_normalized:
  bounded_scaled_mul_ceil64_decimal left right = SOME result ==>
  bounded_signed64_normalized result
Proof
  rw [bounded_scaled_mul_ceil64_decimal_def]
  >> Cases_on `bounded_signed_word64_mul_ceil_decimal left right`
  >> gvs []
  >> imp_res_tac bounded_signed128_narrow64_some
QED

Theorem bounded_interval64_product_from_pairs_decimal_bounds:
  bounded_interval64_product_from_pairs_decimal
    lower_left lower_right upper_left upper_right =
      SOME (BoundedInterval64 lower upper) ==>
  (&1000000000000:int) * bounded_signed64_to_int lower <=
    bounded_signed64_to_int lower_left *
    bounded_signed64_to_int lower_right /\
  bounded_signed64_to_int upper_left *
    bounded_signed64_to_int upper_right <=
    (&1000000000000:int) * bounded_signed64_to_int upper
Proof
  strip_tac
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal lower_left lower_right`
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal upper_left upper_right`
  >> fs [bounded_interval64_product_from_pairs_decimal_def]
  >> metis_tac
       [bounded_scaled_mul_floor64_decimal_lower_bound_general,
        bounded_scaled_mul_ceil64_decimal_upper_bound_general]
QED

Theorem bounded_interval64_product_from_pairs_decimal_contains_product:
  bounded_interval64_product_from_pairs_decimal
    lower_left lower_right upper_left upper_right =
      SOME (BoundedInterval64 lower upper) /\
  bounded_signed64_to_int lower_left *
      bounded_signed64_to_int lower_right <= product /\
  product <= bounded_signed64_to_int upper_left *
      bounded_signed64_to_int upper_right ==>
  (&1000000000000:int) * bounded_signed64_to_int lower <= product /\
  product <= (&1000000000000:int) * bounded_signed64_to_int upper
Proof
  metis_tac [bounded_interval64_product_from_pairs_decimal_bounds,
             integerTheory.INT_LE_TRANS]
QED

Theorem bounded_interval64_product_from_pairs_decimal_normalized:
  bounded_interval64_product_from_pairs_decimal
    lower_left lower_right upper_left upper_right =
      SOME (BoundedInterval64 lower upper) ==>
  bounded_signed64_normalized lower /\
  bounded_signed64_normalized upper
Proof
  rw [bounded_interval64_product_from_pairs_decimal_def]
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal lower_left lower_right`
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal upper_left upper_right`
  >> gvs []
  >> metis_tac [bounded_scaled_mul_floor64_decimal_normalized,
                 bounded_scaled_mul_ceil64_decimal_normalized]
QED

Theorem bounded_interval64_product_mixed_decimal_bounds:
  bounded_interval64_product_mixed_decimal
    left_lower left_upper right_lower right_upper =
      SOME (BoundedInterval64 lower upper) ==>
  (&1000000000000:int) * bounded_signed64_to_int lower <=
      bounded_signed64_to_int left_lower *
      bounded_signed64_to_int right_upper /\
  (&1000000000000:int) * bounded_signed64_to_int lower <=
      bounded_signed64_to_int left_upper *
      bounded_signed64_to_int right_lower /\
  bounded_signed64_to_int left_lower *
      bounded_signed64_to_int right_lower <=
      (&1000000000000:int) * bounded_signed64_to_int upper /\
  bounded_signed64_to_int left_upper *
      bounded_signed64_to_int right_upper <=
      (&1000000000000:int) * bounded_signed64_to_int upper
Proof
  strip_tac
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal left_lower right_upper`
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal left_upper right_lower`
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal left_lower right_lower`
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal left_upper right_upper`
  >> fs [bounded_interval64_product_mixed_decimal_def]
  >> imp_res_tac bounded_scaled_mul_floor64_decimal_lower_bound_general
  >> imp_res_tac bounded_scaled_mul_ceil64_decimal_upper_bound_general
  >> rw [bounded_signed64_min_correct, bounded_signed64_max_correct]
  >> every_case_tac
  >> fs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_product_mixed_decimal_contains_product:
  bounded_interval64_product_mixed_decimal
    left_lower left_upper right_lower right_upper =
      SOME (BoundedInterval64 lower upper) /\
  (bounded_signed64_to_int left_lower *
       bounded_signed64_to_int right_upper <= product \/
   bounded_signed64_to_int left_upper *
       bounded_signed64_to_int right_lower <= product) /\
  (product <= bounded_signed64_to_int left_lower *
       bounded_signed64_to_int right_lower \/
   product <= bounded_signed64_to_int left_upper *
       bounded_signed64_to_int right_upper) ==>
  (&1000000000000:int) * bounded_signed64_to_int lower <= product /\
  product <= (&1000000000000:int) * bounded_signed64_to_int upper
Proof
  metis_tac [bounded_interval64_product_mixed_decimal_bounds,
             integerTheory.INT_LE_TRANS]
QED

Theorem bounded_interval64_mul_unchecked_decimal_contains_product:
  bounded_interval64_valid left /\
  bounded_interval64_valid right /\
  bounded_interval64_contains_int left left_value /\
  bounded_interval64_contains_int right right_value /\
  bounded_interval64_mul_unchecked_decimal left right =
    SOME (BoundedInterval64 lower upper) ==>
  (&1000000000000:int) * bounded_signed64_to_int lower <=
      left_value * right_value /\
  left_value * right_value <=
      (&1000000000000:int) * bounded_signed64_to_int upper
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_interval64_mul_unchecked_decimal
          (BoundedInterval64 left_lower left_upper)
          (BoundedInterval64 right_lower right_upper) = _`
  >> simp [bounded_interval64_valid_def,
           bounded_interval64_contains_int_def,
           bounded_signed64_le_correct]
  >> strip_tac
  >> Cases_on `bounded_signed64_nonnegative left_lower`
  >- (Cases_on `bounded_signed64_nonnegative right_lower`
      >- (fs [bounded_interval64_mul_unchecked_decimal_def,
              bounded_signed64_nonnegative_correct,
              bounded_signed64_nonpositive_correct]
          >> `bounded_signed64_to_int left_lower *
                bounded_signed64_to_int right_lower <=
                left_value * right_value /\
              left_value * right_value <=
                bounded_signed64_to_int left_upper *
                bounded_signed64_to_int right_upper` by
               (irule bounded_int_product_bounds_nonnegative_nonnegative
                >> simp [])
          >> metis_tac
               [bounded_interval64_product_from_pairs_decimal_contains_product])
      >> Cases_on `bounded_signed64_nonpositive right_upper`
      >- (fs [bounded_interval64_mul_unchecked_decimal_def,
              bounded_signed64_nonnegative_correct,
              bounded_signed64_nonpositive_correct]
          >> `bounded_signed64_to_int left_upper *
                bounded_signed64_to_int right_lower <=
                left_value * right_value /\
              left_value * right_value <=
                bounded_signed64_to_int left_lower *
                bounded_signed64_to_int right_upper` by
               (irule bounded_int_product_bounds_nonnegative_nonpositive
                >> simp [])
          >> metis_tac
               [bounded_interval64_product_from_pairs_decimal_contains_product])
      >> fs [bounded_interval64_mul_unchecked_decimal_def,
             bounded_signed64_nonnegative_correct,
             bounded_signed64_nonpositive_correct]
      >> `bounded_signed64_to_int left_upper *
            bounded_signed64_to_int right_lower <=
            left_value * right_value /\
          left_value * right_value <=
            bounded_signed64_to_int left_upper *
            bounded_signed64_to_int right_upper` by
           (irule bounded_int_product_bounds_nonnegative_mixed
            >> intLib.ARITH_TAC)
      >> metis_tac
           [bounded_interval64_product_from_pairs_decimal_contains_product])
  >> Cases_on `bounded_signed64_nonpositive left_upper`
  >- (Cases_on `bounded_signed64_nonnegative right_lower`
      >- (fs [bounded_interval64_mul_unchecked_decimal_def,
              bounded_signed64_nonnegative_correct,
              bounded_signed64_nonpositive_correct]
          >> `bounded_signed64_to_int left_lower *
                bounded_signed64_to_int right_upper <=
                left_value * right_value /\
              left_value * right_value <=
                bounded_signed64_to_int left_upper *
                bounded_signed64_to_int right_lower` by
               (irule bounded_int_product_bounds_nonpositive_nonnegative
                >> simp [])
          >> metis_tac
               [bounded_interval64_product_from_pairs_decimal_contains_product])
      >> Cases_on `bounded_signed64_nonpositive right_upper`
      >- (fs [bounded_interval64_mul_unchecked_decimal_def,
              bounded_signed64_nonnegative_correct,
              bounded_signed64_nonpositive_correct]
          >> `bounded_signed64_to_int left_upper *
                bounded_signed64_to_int right_upper <=
                left_value * right_value /\
              left_value * right_value <=
                bounded_signed64_to_int left_lower *
                bounded_signed64_to_int right_lower` by
               (irule bounded_int_product_bounds_nonpositive_nonpositive
                >> simp [])
          >> metis_tac
               [bounded_interval64_product_from_pairs_decimal_contains_product])
      >> fs [bounded_interval64_mul_unchecked_decimal_def,
             bounded_signed64_nonnegative_correct,
             bounded_signed64_nonpositive_correct]
      >> `bounded_signed64_to_int left_lower *
            bounded_signed64_to_int right_upper <=
            left_value * right_value /\
          left_value * right_value <=
            bounded_signed64_to_int left_lower *
            bounded_signed64_to_int right_lower` by
           (irule bounded_int_product_bounds_nonpositive_mixed
            >> intLib.ARITH_TAC)
      >> metis_tac
           [bounded_interval64_product_from_pairs_decimal_contains_product])
  >> Cases_on `bounded_signed64_nonnegative right_lower`
  >- (fs [bounded_interval64_mul_unchecked_decimal_def,
          bounded_signed64_nonnegative_correct,
          bounded_signed64_nonpositive_correct]
      >> `bounded_signed64_to_int left_lower *
            bounded_signed64_to_int right_upper <=
            left_value * right_value /\
          left_value * right_value <=
            bounded_signed64_to_int left_upper *
            bounded_signed64_to_int right_upper` by
           (irule bounded_int_product_bounds_mixed_nonnegative
            >> intLib.ARITH_TAC)
      >> metis_tac
           [bounded_interval64_product_from_pairs_decimal_contains_product])
  >> Cases_on `bounded_signed64_nonpositive right_upper`
  >- (fs [bounded_interval64_mul_unchecked_decimal_def,
          bounded_signed64_nonnegative_correct,
          bounded_signed64_nonpositive_correct]
      >> `bounded_signed64_to_int left_upper *
            bounded_signed64_to_int right_lower <=
            left_value * right_value /\
          left_value * right_value <=
            bounded_signed64_to_int left_lower *
            bounded_signed64_to_int right_lower` by
           (irule bounded_int_product_bounds_mixed_nonpositive
            >> intLib.ARITH_TAC)
      >> metis_tac
           [bounded_interval64_product_from_pairs_decimal_contains_product])
  >> fs [bounded_interval64_mul_unchecked_decimal_def,
         bounded_signed64_nonnegative_correct,
         bounded_signed64_nonpositive_correct]
  >> `(bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper <=
          left_value * right_value \/
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower <=
          left_value * right_value) /\
      (left_value * right_value <=
          bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower \/
       left_value * right_value <=
          bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper)` by
       (irule bounded_int_product_bounds_mixed_mixed
        >> intLib.ARITH_TAC)
  >> metis_tac
       [bounded_interval64_product_mixed_decimal_contains_product]
QED

Theorem bounded_interval64_mul_decimal_contains_product:
  bounded_interval64_contains_int left left_value /\
  bounded_interval64_contains_int right right_value /\
  bounded_interval64_mul_decimal left right =
    SOME (BoundedInterval64 lower upper) ==>
  (&1000000000000:int) * bounded_signed64_to_int lower <=
      left_value * right_value /\
  left_value * right_value <=
      (&1000000000000:int) * bounded_signed64_to_int upper
Proof
  strip_tac
  >> Cases_on
       `bounded_interval64_valid left /\ bounded_interval64_valid right`
  >- (fs [bounded_interval64_mul_decimal_def]
      >> irule bounded_interval64_mul_unchecked_decimal_contains_product
      >> metis_tac [])
  >> fs [bounded_interval64_mul_decimal_def]
  >> metis_tac []
QED

Theorem bounded_interval64_mul_decimal_contains_scaled_product:
  bounded_interval64_contains_int left left_value /\
  bounded_interval64_contains_int right right_value /\
  bounded_interval64_mul_decimal left right = SOME result ==>
  bounded_interval64_contains_scaled_int result
    (&1000000000000:int) (left_value * right_value)
Proof
  strip_tac
  >> Cases_on `result`
  >> fs [bounded_interval64_contains_scaled_int_def]
  >> metis_tac [bounded_interval64_mul_decimal_contains_product]
QED

Theorem bounded_scaled_mul_decimal_exact_test:
  bounded_scaled_mul_floor64_decimal
    (BoundedSigned64 F 1500000000000w)
    (BoundedSigned64 T 2000000000000w) =
      SOME (BoundedSigned64 T 3000000000000w) /\
  bounded_scaled_mul_ceil64_decimal
    (BoundedSigned64 F 1500000000000w)
    (BoundedSigned64 T 2000000000000w) =
      SOME (BoundedSigned64 T 3000000000000w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_scaled_mul_decimal_directed_test:
  bounded_scaled_mul_floor64_decimal
    (BoundedSigned64 T 1000000000001w)
    (BoundedSigned64 F 1000000000001w) =
      SOME (BoundedSigned64 T 1000000000003w) /\
  bounded_scaled_mul_ceil64_decimal
    (BoundedSigned64 T 1000000000001w)
    (BoundedSigned64 F 1000000000001w) =
      SOME (BoundedSigned64 T 1000000000002w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
