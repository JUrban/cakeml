(*****************************************************************************
 * Signed word-only 192-bit arithmetic and the two Taylor rounding scales.
 *
 * This DEVELOPMENT layer supplies the concrete signed accumulator needed by
 * the compact nonlinear checker.  Every operation is total and reports
 * overflow through option.  General refinement to the mathematical integer
 * and directed-rounding contracts remains a release obligation; the closed
 * tests below exercise sign cancellation, overflow, limb shifts, and both
 * directed branches used by Taylor completion.
 *****************************************************************************)
Theory compute_boundedWideSigned
Ancestors
  compute_boundedWide compute_boundedSignedEndpoint
Libs
  bossLib preamble intLib

Datatype:
  bounded_signed192 = BoundedSigned192 bool bounded192
End

Definition bounded192_is_zero_def:
  bounded192_is_zero (Bounded192 high middle low) =
    (high = 0w ∧ middle = 0w ∧ low = 0w)
End

Definition bounded_signed192_to_int_def:
  bounded_signed192_to_int (BoundedSigned192 negative magnitude) =
    if negative then -&(bounded192_to_num magnitude)
    else &(bounded192_to_num magnitude)
End

Definition bounded_signed192_make_def:
  bounded_signed192_make negative magnitude =
    BoundedSigned192 (negative ∧ ¬bounded192_is_zero magnitude) magnitude
End

Definition bounded_signed192_normalized_def:
  bounded_signed192_normalized (BoundedSigned192 negative magnitude) ⇔
    ¬negative ∨ ¬bounded192_is_zero magnitude
End

Definition bounded_signed192_add_def:
  bounded_signed192_add
      (BoundedSigned192 left_negative left_magnitude)
      (BoundedSigned192 right_negative right_magnitude) =
    if left_negative = right_negative then
      case bounded192_add_words left_magnitude right_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed192_make left_negative magnitude)
    else if bounded192_le_words left_magnitude right_magnitude then
      case bounded192_sub_words right_magnitude left_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed192_make right_negative magnitude)
    else
      case bounded192_sub_words left_magnitude right_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed192_make left_negative magnitude)
End

(* Multiplication by 2^81 = 2 * (2^40)^2 for a stored endpoint. *)
Definition bounded_signed64_scale81_def:
  bounded_signed64_scale81 (BoundedSigned64 negative magnitude) =
    bounded_signed192_make negative
      (Bounded192 (magnitude >>> 47) (magnitude << 17) 0w)
End

(* Multiplication by 2^41 = 2 * 2^40 for the linear Taylor term. *)
Definition bounded128_scale41_def:
  bounded128_scale41 (Bounded128 high low) =
    Bounded192
      (high >>> 23)
      ((low >>> 23) + (high << 41))
      (low << 41)
End

(* Quotient and remainder discriminator for division by 2^81. *)
Definition bounded192_shift_floor81_words_def:
  bounded192_shift_floor81_words (Bounded192 high middle low) =
    Bounded128
      (high >>> 17)
      ((middle >>> 17) + (high << 47))
End

Definition bounded192_low81_nonzero_def:
  bounded192_low81_nonzero (Bounded192 high middle low) =
    (low ≠ 0w ∨ word_and middle 131071w ≠ 0w)
End

Definition bounded_signed128_narrow64_option_def:
  bounded_signed128_narrow64_option negative source =
    case source of
    | NONE => NONE
    | SOME magnitude =>
        bounded_signed128_narrow64
          (bounded_signed128_make negative magnitude)
End

Definition bounded_signed192_shift_floor81_64_def:
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 negative magnitude) =
    let quotient = bounded192_shift_floor81_words magnitude in
    if negative ∧ bounded192_low81_nonzero magnitude then
      bounded_signed128_narrow64_option T
        (bounded128_add_words quotient (Bounded128 0w 1w))
    else
      bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Definition bounded_signed192_shift_ceil81_64_def:
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 negative magnitude) =
    let quotient = bounded192_shift_floor81_words magnitude in
    if ¬negative ∧ bounded192_low81_nonzero magnitude then
      bounded_signed128_narrow64_option F
        (bounded128_add_words quotient (Bounded128 0w 1w))
    else
      bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Theorem bounded192_is_zero_iff:
  bounded192_is_zero magnitude ⇔ bounded192_to_num magnitude = 0
Proof
  Cases_on `magnitude`
  >> simp [bounded192_is_zero_def,
           compute_boundedTheory.bounded192_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           wordsTheory.w2n_eq_0]
QED

Theorem bounded_signed192_make_value:
  bounded_signed192_to_int (bounded_signed192_make negative magnitude) =
  (if negative then -&(bounded192_to_num magnitude)
   else &(bounded192_to_num magnitude))
Proof
  Cases_on `negative`
  >> Cases_on `bounded192_is_zero magnitude`
  >> fs [bounded_signed192_make_def, bounded_signed192_to_int_def,
         bounded192_is_zero_iff]
QED

Theorem bounded_signed192_make_normalized:
  bounded_signed192_normalized
    (bounded_signed192_make negative magnitude)
Proof
  Cases_on `negative`
  >> simp [bounded_signed192_make_def, bounded_signed192_normalized_def]
QED

Theorem bounded_signed192_make_option_normalized:
  (case source of
   | NONE => NONE
   | SOME magnitude => SOME (bounded_signed192_make negative magnitude)) =
    SOME result ⇒
  bounded_signed192_normalized result
Proof
  Cases_on `source`
  >> fs []
  >> metis_tac [bounded_signed192_make_normalized]
QED

Theorem bounded_signed192_add_normalized:
  bounded_signed192_add left right = SOME result ⇒
  bounded_signed192_normalized result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed192_add_def]
  >> metis_tac [bounded_signed192_make_option_normalized]
QED

Theorem bounded_signed192_add_value:
  bounded_signed192_add left right = SOME result ⇒
  bounded_signed192_to_int result =
    bounded_signed192_to_int left + bounded_signed192_to_int right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_signed192_add
          (BoundedSigned192 left_negative left_magnitude)
          (BoundedSigned192 right_negative right_magnitude) = SOME result`
  >> Cases_on `left_negative = right_negative`
  >- (fs []
      >> rw [bounded_signed192_add_def]
      >> Cases_on `bounded192_add_words left_magnitude right_magnitude`
      >> gvs [compute_boundedTheory.bounded192_add_words_refines,
              bounded_signed192_make_value,
              bounded_signed192_to_int_def]
      >> imp_res_tac compute_boundedTheory.bounded192_add_some
      >> Cases_on `left_negative`
      >> fs []
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded192_le_words left_magnitude right_magnitude`
  >> rw [bounded_signed192_add_def]
  >- (Cases_on `bounded192_sub_words right_magnitude left_magnitude`
      >> gvs []
      >> imp_res_tac compute_boundedWideTheory.bounded192_sub_words_some
      >> Cases_on `left_negative`
      >> Cases_on `right_negative`
      >> fs [bounded_signed192_make_value,
             bounded_signed192_to_int_def,
             compute_boundedWideTheory.bounded192_le_words_correct]
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded192_sub_words left_magnitude right_magnitude`
  >> gvs []
  >> imp_res_tac compute_boundedWideTheory.bounded192_sub_words_some
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [bounded_signed192_make_value,
         bounded_signed192_to_int_def,
         compute_boundedWideTheory.bounded192_le_words_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_wide_signed_closed_tests:
  bounded_signed192_add
      (BoundedSigned192 F (Bounded192 0w 0w 7w))
      (BoundedSigned192 T (Bounded192 0w 0w 3w)) =
    SOME (BoundedSigned192 F (Bounded192 0w 0w 4w)) ∧
  bounded_signed192_add
      (BoundedSigned192 T (Bounded192 0w 0w 7w))
      (BoundedSigned192 F (Bounded192 0w 0w 7w)) =
    SOME (BoundedSigned192 F (Bounded192 0w 0w 0w)) ∧
  bounded_signed192_add
      (BoundedSigned192 F (Bounded192 (-1w) (-1w) (-1w)))
      (BoundedSigned192 F (Bounded192 0w 0w 1w)) = NONE ∧
  bounded_signed64_scale81 (BoundedSigned64 F 3w) =
    BoundedSigned192 F (Bounded192 0w 393216w 0w) ∧
  bounded128_scale41 (Bounded128 0w 3w) =
    Bounded192 0w 0w 6597069766656w ∧
  bounded192_shift_floor81_words (Bounded192 0w 393216w 0w) =
    Bounded128 0w 3w ∧
  ¬bounded192_low81_nonzero (Bounded192 0w 393216w 0w) ∧
  bounded192_low81_nonzero (Bounded192 0w 393216w 1w) ∧
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 F (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 F 3w) ∧
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 F (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 F 4w) ∧
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 T (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 T 4w) ∧
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 T (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 T 3w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
