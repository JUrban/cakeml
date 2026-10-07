(*****************************************************************************
 * Sign-classified one-word interval products for the nonlinear executor.
 *
 * The hot unchecked operation is used only after a source/input validator
 * establishes interval validity and later preservation theorems discharge
 * it generally.  The checked wrapper is fail-closed for external inputs.
 * Every directed product is widened, rounded at 2^40, and narrowed through
 * the explicit endpoint overflow boundary.
 *****************************************************************************)
Theory compute_boundedInterval
Ancestors
  compute_boundedSignedEndpoint compute_boundedSigned
Libs
  bossLib

Datatype:
  bounded_interval64 = BoundedInterval64 bounded_signed64 bounded_signed64
End

Definition bounded_interval64_lower_def:
  bounded_interval64_lower (BoundedInterval64 lower upper) = lower
End

Definition bounded_interval64_upper_def:
  bounded_interval64_upper (BoundedInterval64 lower upper) = upper
End

Definition bounded_interval64_valid_def:
  bounded_interval64_valid (BoundedInterval64 lower upper) ⇔
    bounded_signed64_normalized lower ∧
    bounded_signed64_normalized upper ∧
    bounded_signed64_le lower upper
End

Definition bounded_signed64_nonnegative_def:
  bounded_signed64_nonnegative value =
    ¬bounded_signed64_effective_negative value
End

Definition bounded_signed64_nonpositive_def:
  bounded_signed64_nonpositive value =
    (bounded_signed64_effective_negative value ∨
     bounded_signed64_magnitude value = 0w)
End

Definition bounded_scaled_mul_floor64_def:
  bounded_scaled_mul_floor64 left right =
    case bounded_signed_word64_mul_floor40 left right of
    | NONE => NONE
    | SOME wide => bounded_signed128_narrow64 wide
End

Definition bounded_scaled_mul_ceil64_def:
  bounded_scaled_mul_ceil64 left right =
    case bounded_signed_word64_mul_ceil40 left right of
    | NONE => NONE
    | SOME wide => bounded_signed128_narrow64 wide
End

Definition bounded_interval64_product_from_pairs_def:
  bounded_interval64_product_from_pairs
      lower_left lower_right upper_left upper_right =
    case bounded_scaled_mul_floor64 lower_left lower_right of
    | NONE => NONE
    | SOME lower =>
        case bounded_scaled_mul_ceil64 upper_left upper_right of
        | NONE => NONE
        | SOME upper => SOME (BoundedInterval64 lower upper)
End

Definition bounded_interval64_product_mixed_def:
  bounded_interval64_product_mixed
      left_lower left_upper right_lower right_upper =
    case bounded_scaled_mul_floor64 left_lower right_upper of
    | NONE => NONE
    | SOME lower_left =>
      case bounded_scaled_mul_floor64 left_upper right_lower of
      | NONE => NONE
      | SOME lower_right =>
        case bounded_scaled_mul_ceil64 left_lower right_lower of
        | NONE => NONE
        | SOME upper_left =>
          case bounded_scaled_mul_ceil64 left_upper right_upper of
          | NONE => NONE
          | SOME upper_right =>
              SOME
                (BoundedInterval64
                  (bounded_signed64_min lower_left lower_right)
                  (bounded_signed64_max upper_left upper_right))
End

Definition bounded_interval64_mul_unchecked_def:
  bounded_interval64_mul_unchecked
      (BoundedInterval64 left_lower left_upper)
      (BoundedInterval64 right_lower right_upper) =
    if bounded_signed64_nonnegative left_lower then
      if bounded_signed64_nonnegative right_lower then
        bounded_interval64_product_from_pairs
          left_lower right_lower left_upper right_upper
      else if bounded_signed64_nonpositive right_upper then
        bounded_interval64_product_from_pairs
          left_upper right_lower left_lower right_upper
      else
        bounded_interval64_product_from_pairs
          left_upper right_lower left_upper right_upper
    else if bounded_signed64_nonpositive left_upper then
      if bounded_signed64_nonnegative right_lower then
        bounded_interval64_product_from_pairs
          left_lower right_upper left_upper right_lower
      else if bounded_signed64_nonpositive right_upper then
        bounded_interval64_product_from_pairs
          left_upper right_upper left_lower right_lower
      else
        bounded_interval64_product_from_pairs
          left_lower right_upper left_lower right_lower
    else if bounded_signed64_nonnegative right_lower then
      bounded_interval64_product_from_pairs
        left_lower right_upper left_upper right_upper
    else if bounded_signed64_nonpositive right_upper then
      bounded_interval64_product_from_pairs
        left_upper right_lower left_lower right_lower
    else
      bounded_interval64_product_mixed
        left_lower left_upper right_lower right_upper
End

Definition bounded_interval64_mul_def:
  bounded_interval64_mul left right =
    if bounded_interval64_valid left ∧ bounded_interval64_valid right then
      bounded_interval64_mul_unchecked left right
    else NONE
End

Theorem bounded_scaled_mul_floor64_normalized:
  bounded_scaled_mul_floor64 left right = SOME result ⇒
  bounded_signed64_normalized result
Proof
  rw [bounded_scaled_mul_floor64_def]
  >> Cases_on `bounded_signed_word64_mul_floor40 left right`
  >> gvs []
  >> imp_res_tac bounded_signed128_narrow64_some
QED

Theorem bounded_scaled_mul_ceil64_normalized:
  bounded_scaled_mul_ceil64 left right = SOME result ⇒
  bounded_signed64_normalized result
Proof
  rw [bounded_scaled_mul_ceil64_def]
  >> Cases_on `bounded_signed_word64_mul_ceil40 left right`
  >> gvs []
  >> imp_res_tac bounded_signed128_narrow64_some
QED

Theorem bounded_interval64_product_from_pairs_normalized:
  bounded_interval64_product_from_pairs
    lower_left lower_right upper_left upper_right =
      SOME (BoundedInterval64 lower upper) ⇒
  bounded_signed64_normalized lower ∧
  bounded_signed64_normalized upper
Proof
  rw [bounded_interval64_product_from_pairs_def]
  >> Cases_on `bounded_scaled_mul_floor64 lower_left lower_right`
  >> Cases_on `bounded_scaled_mul_ceil64 upper_left upper_right`
  >> gvs []
  >> metis_tac [bounded_scaled_mul_floor64_normalized,
                 bounded_scaled_mul_ceil64_normalized]
QED

Theorem bounded_interval64_rejects_invalid:
  ¬bounded_interval64_valid left ∨ ¬bounded_interval64_valid right ⇒
  bounded_interval64_mul left right = NONE
Proof
  rw [bounded_interval64_mul_def]
  >> fs []
QED

Theorem bounded_interval64_sign_class_tests:
  bounded_signed64_nonnegative (BoundedSigned64 T 0w) ∧
  bounded_signed64_nonpositive (BoundedSigned64 T 0w) ∧
  bounded_signed64_nonnegative (BoundedSigned64 F 7w) ∧
  ¬bounded_signed64_nonpositive (BoundedSigned64 F 7w) ∧
  ¬bounded_signed64_nonnegative (BoundedSigned64 T 7w) ∧
  bounded_signed64_nonpositive (BoundedSigned64 T 7w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_exact_sign_class_tests:
  let p2 = BoundedSigned64 F 2199023255552w in
  let p3 = BoundedSigned64 F 3298534883328w in
  let p4 = BoundedSigned64 F 4398046511104w in
  let p5 = BoundedSigned64 F 5497558138880w in
  let n2 = BoundedSigned64 T 2199023255552w in
  let n3 = BoundedSigned64 T 3298534883328w in
  let n4 = BoundedSigned64 T 4398046511104w in
  let n6 = BoundedSigned64 T 6597069766656w in
  let p6 = BoundedSigned64 F 6597069766656w in
  bounded_interval64_mul
    (BoundedInterval64 p2 p2) (BoundedInterval64 p3 p3) =
      SOME (BoundedInterval64 p6 p6) ∧
  bounded_interval64_mul
    (BoundedInterval64 p2 p2) (BoundedInterval64 n3 n3) =
      SOME (BoundedInterval64 n6 n6) ∧
  bounded_interval64_mul
    (BoundedInterval64 n2 n2) (BoundedInterval64 n3 n3) =
      SOME (BoundedInterval64 p6 p6) ∧
  bounded_interval64_mul
    (BoundedInterval64 n2 p3) (BoundedInterval64 n4 p5) =
      SOME
        (BoundedInterval64
          (BoundedSigned64 T 13194139533312w)
          (BoundedSigned64 F 16492674416640w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_overflow_test:
  bounded_interval64_mul
    (BoundedInterval64 (BoundedSigned64 F (-1w))
                       (BoundedSigned64 F (-1w)))
    (BoundedInterval64 (BoundedSigned64 F (-1w))
                       (BoundedSigned64 F (-1w))) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
