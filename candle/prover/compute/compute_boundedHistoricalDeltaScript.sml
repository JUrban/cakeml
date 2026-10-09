(*****************************************************************************
 * Fixed-layout historical delta value at the shared 2^40 scale.
 *
 * The historical Flyspeck enclosure deliberately rounds a complete cubic
 * block only once.  Two stored endpoints therefore form an exact signed
 * 128-bit product, and the third factor plus the block accumulation require
 * a signed 192-bit transient.  Every operation is total and returns NONE on
 * overflow.  This DEVELOPMENT layer establishes the executable boundary;
 * its general integer/interval refinement remains a release obligation.
 *****************************************************************************)
Theory compute_boundedHistoricalDelta
Ancestors
  compute_boundedTaylorMul compute_boundedDeltaTaylor
Libs
  bossLib preamble intLib

Definition bounded_signed192_le_words_def:
  bounded_signed192_le_words
      (BoundedSigned192 left_negative left_magnitude)
      (BoundedSigned192 right_negative right_magnitude) =
    if left_negative then
      if right_negative then
        bounded192_le_words right_magnitude left_magnitude
      else T
    else if right_negative then F
    else bounded192_le_words left_magnitude right_magnitude
End

Definition bounded_signed192_min_def:
  bounded_signed192_min left right =
    if bounded_signed192_le_words left right then left else right
End

Definition bounded_signed192_max_def:
  bounded_signed192_max left right =
    if bounded_signed192_le_words left right then right else left
End

Definition bounded_signed192_neg_def:
  bounded_signed192_neg (BoundedSigned192 negative magnitude) =
    bounded_signed192_make (¬negative) magnitude
End

Definition bounded_signed128_nonnegative_def:
  bounded_signed128_nonnegative (BoundedSigned128 negative magnitude) =
    ¬negative
End

Definition bounded_signed128_nonpositive_def:
  bounded_signed128_nonpositive (BoundedSigned128 negative magnitude) =
    (negative ∨ bounded128_is_zero magnitude)
End

Definition bounded_signed128_mul_signed64_raw192_def:
  bounded_signed128_mul_signed64_raw192
      (BoundedSigned128 left_negative left_magnitude)
      (BoundedSigned64 right_negative right_magnitude) =
    case bounded128_mul_word64_to_192_words left_magnitude right_magnitude of
    | NONE => NONE
    | SOME magnitude =>
        SOME (bounded_signed192_make
          (¬(left_negative = right_negative)) magnitude)
End

Definition bounded_raw128_interval_product_from_pairs_def:
  bounded_raw128_interval_product_from_pairs
      lower_left lower_right upper_left upper_right =
    case bounded_signed128_mul_signed64_raw192 lower_left lower_right of
    | NONE => NONE
    | SOME lower =>
      case bounded_signed128_mul_signed64_raw192 upper_left upper_right of
      | NONE => NONE
      | SOME upper => SOME (lower,upper)
End

Definition bounded_raw128_interval_product_mixed_def:
  bounded_raw128_interval_product_mixed
      left_lower left_upper right_lower right_upper =
    case bounded_signed128_mul_signed64_raw192 left_lower right_upper of
    | NONE => NONE
    | SOME lower_left =>
      case bounded_signed128_mul_signed64_raw192 left_upper right_lower of
      | NONE => NONE
      | SOME lower_right =>
        case bounded_signed128_mul_signed64_raw192 left_lower right_lower of
        | NONE => NONE
        | SOME upper_left =>
          case bounded_signed128_mul_signed64_raw192 left_upper right_upper of
          | NONE => NONE
          | SOME upper_right =>
              SOME
                (bounded_signed192_min lower_left lower_right,
                 bounded_signed192_max upper_left upper_right)
End

Definition bounded_raw128_interval_mul64_unchecked_def:
  bounded_raw128_interval_mul64_unchecked
      (left_lower,left_upper)
      (BoundedInterval64 right_lower right_upper) =
    if bounded_signed128_nonnegative left_lower then
      if bounded_signed64_nonnegative right_lower then
        bounded_raw128_interval_product_from_pairs
          left_lower right_lower left_upper right_upper
      else if bounded_signed64_nonpositive right_upper then
        bounded_raw128_interval_product_from_pairs
          left_upper right_lower left_lower right_upper
      else
        bounded_raw128_interval_product_from_pairs
          left_upper right_lower left_upper right_upper
    else if bounded_signed128_nonpositive left_upper then
      if bounded_signed64_nonnegative right_lower then
        bounded_raw128_interval_product_from_pairs
          left_lower right_upper left_upper right_lower
      else if bounded_signed64_nonpositive right_upper then
        bounded_raw128_interval_product_from_pairs
          left_upper right_upper left_lower right_lower
      else
        bounded_raw128_interval_product_from_pairs
          left_lower right_upper left_lower right_lower
    else if bounded_signed64_nonnegative right_lower then
      bounded_raw128_interval_product_from_pairs
        left_lower right_upper left_upper right_upper
    else if bounded_signed64_nonpositive right_upper then
      bounded_raw128_interval_product_from_pairs
        left_upper right_lower left_lower right_lower
    else
      bounded_raw128_interval_product_mixed
        left_lower left_upper right_lower right_upper
End

Definition bounded_historical_raw_cubic_def:
  bounded_historical_raw_cubic first second third =
    if ¬bounded_interval64_valid first ∨
       ¬bounded_interval64_valid second ∨
       ¬bounded_interval64_valid third
    then NONE
    else
      bounded_raw128_interval_mul64_unchecked
        (bounded_interval64_raw_mul_bounds_unchecked first second) third
End

Definition bounded_historical_raw_cubic_signed_def:
  bounded_historical_raw_cubic_signed first second third negative =
    case bounded_historical_raw_cubic first second third of
    | NONE => NONE
    | SOME (lower,upper) =>
        if negative then
          SOME (bounded_signed192_neg upper,bounded_signed192_neg lower)
        else SOME (lower,upper)
End

Definition bounded_historical_raw_cubics_def:
  bounded_historical_raw_cubics [] = SOME [] ∧
  bounded_historical_raw_cubics
      ((first,second,third,negative)::rest) =
    case bounded_historical_raw_cubic_signed
      first second third negative of
    | NONE => NONE
    | SOME value =>
      case bounded_historical_raw_cubics rest of
      | NONE => NONE
      | SOME values => SOME (value::values)
End

Definition bounded_signed192_interval_sum_aux_def:
  bounded_signed192_interval_sum_aux [] lower upper = SOME (lower,upper) ∧
  bounded_signed192_interval_sum_aux ((entry_lower,entry_upper)::rest)
      lower upper =
    case bounded_signed192_add lower entry_lower of
    | NONE => NONE
    | SOME next_lower =>
      case bounded_signed192_add upper entry_upper of
      | NONE => NONE
      | SOME next_upper =>
          bounded_signed192_interval_sum_aux rest next_lower next_upper
End

Definition bounded_signed192_interval_sum_def:
  bounded_signed192_interval_sum values =
    let zero = bounded_signed192_make F bounded192_zero in
    bounded_signed192_interval_sum_aux values zero zero
End

Definition bounded192_shift_floor80_words_def:
  bounded192_shift_floor80_words (Bounded192 high middle low) =
    Bounded128 (high >>> 16) ((high << 48) + (middle >>> 16))
End

Definition bounded192_low80_nonzero_def:
  bounded192_low80_nonzero (Bounded192 high middle low) =
    (low ≠ 0w ∨ word_and middle 65535w ≠ 0w)
End

Definition bounded_signed192_shift_floor80_64_def:
  bounded_signed192_shift_floor80_64
      (BoundedSigned192 negative magnitude) =
    let quotient = bounded192_shift_floor80_words magnitude in
    if negative ∧ bounded192_low80_nonzero magnitude then
      bounded_signed128_narrow64_option T
        (bounded128_add_words quotient (Bounded128 0w 1w))
    else
      bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Definition bounded_signed192_shift_ceil80_64_def:
  bounded_signed192_shift_ceil80_64
      (BoundedSigned192 negative magnitude) =
    let quotient = bounded192_shift_floor80_words magnitude in
    if ¬negative ∧ bounded192_low80_nonzero magnitude then
      bounded_signed128_narrow64_option F
        (bounded128_add_words quotient (Bounded128 0w 1w))
    else
      bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Definition bounded_historical_raw_round80_def:
  bounded_historical_raw_round80 (lower,upper) =
    case bounded_signed192_shift_floor80_64 lower of
    | NONE => NONE
    | SOME rounded_lower =>
      case bounded_signed192_shift_ceil80_64 upper of
      | NONE => NONE
      | SOME rounded_upper =>
          SOME (BoundedInterval64 rounded_lower rounded_upper)
End

Definition bounded_historical_delta64_value_six_def:
  bounded_historical_delta64_value_six x0 x1 x2 x3 x4 x5 =
    case bounded_interval64_sum
      [bounded_interval64_neg x0;x1;x2;
       bounded_interval64_neg x3;x4;x5] of
    | NONE => NONE
    | SOME first_linear =>
      case bounded_interval64_sum
        [x0;bounded_interval64_neg x1;x2;x3;
         bounded_interval64_neg x4;x5] of
      | NONE => NONE
      | SOME second_linear =>
        case bounded_interval64_sum
          [x0;x1;bounded_interval64_neg x2;x3;x4;
           bounded_interval64_neg x5] of
        | NONE => NONE
        | SOME third_linear =>
          case bounded_historical_raw_cubics
            [(x0,x3,first_linear,F);
             (x1,x4,second_linear,F);
             (x2,x5,third_linear,F);
             (x1,x2,x3,T);
             (x0,x2,x4,T);
             (x0,x1,x5,T);
             (x3,x4,x5,T)] of
          | NONE => NONE
          | SOME raw_terms =>
            case bounded_signed192_interval_sum raw_terms of
            | NONE => NONE
            | SOME raw => bounded_historical_raw_round80 raw
End

Definition bounded_historical_delta64_value_def:
  bounded_historical_delta64_value environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
        bounded_historical_delta64_value_six x0 x1 x2 x3 x4 x5
    | _ => NONE
End

Theorem bounded_signed192_le_words_correct:
  bounded_signed192_normalized left ∧
  bounded_signed192_normalized right ⇒
  (bounded_signed192_le_words left right ⇔
   bounded_signed192_to_int left ≤ bounded_signed192_to_int right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> rw [bounded_signed192_le_words_def,
         compute_boundedWideSignedTheory.bounded_signed192_normalized_def,
         compute_boundedWideSignedTheory.bounded_signed192_to_int_def,
         compute_boundedWideTheory.bounded192_le_words_correct]
  >> fs [compute_boundedWideSignedTheory.bounded192_is_zero_iff]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed192_min_value:
  bounded_signed192_normalized left ∧
  bounded_signed192_normalized right ⇒
  bounded_signed192_to_int (bounded_signed192_min left right) =
    (if bounded_signed192_to_int left ≤ bounded_signed192_to_int right then
       bounded_signed192_to_int left
     else bounded_signed192_to_int right)
Proof
  rw [bounded_signed192_min_def, bounded_signed192_le_words_correct]
QED

Theorem bounded_signed192_max_value:
  bounded_signed192_normalized left ∧
  bounded_signed192_normalized right ⇒
  bounded_signed192_to_int (bounded_signed192_max left right) =
    (if bounded_signed192_to_int left ≤ bounded_signed192_to_int right then
       bounded_signed192_to_int right
     else bounded_signed192_to_int left)
Proof
  rw [bounded_signed192_max_def, bounded_signed192_le_words_correct]
QED

Theorem bounded_signed192_neg_value:
  bounded_signed192_to_int (bounded_signed192_neg value) =
  -bounded_signed192_to_int value
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `bounded192_is_zero magnitude`
  >> simp [bounded_signed192_neg_def,
           compute_boundedWideSignedTheory.bounded_signed192_make_value,
           compute_boundedWideSignedTheory.bounded_signed192_to_int_def,
           compute_boundedWideSignedTheory.bounded192_is_zero_iff]
QED

Theorem bounded_signed192_neg_normalized:
  bounded_signed192_normalized (bounded_signed192_neg value)
Proof
  Cases_on `value`
  >> simp [bounded_signed192_neg_def,
           compute_boundedWideSignedTheory.bounded_signed192_make_normalized]
QED

Theorem bounded_historical_delta64_point_one_test:
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2199023255552w)
    (BoundedSigned64 F 2199023255552w) in
  bounded_historical_delta64_value (REPLICATE 6 one) = SOME two
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_historical_delta64_shape_rejects:
  bounded_historical_delta64_value [] = NONE ∧
  bounded_historical_delta64_value
    [BoundedInterval64 (BoundedSigned64 F 0w)
      (BoundedSigned64 F 0w)] = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
