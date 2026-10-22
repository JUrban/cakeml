(*****************************************************************************
 * Stored signed endpoints for the fixed-width nonlinear executor.
 *
 * Native range evidence says every stored endpoint fits one word, while raw
 * products and accumulations require wider values.  This layer makes that
 * boundary executable and fail-closed: narrowing rejects a nonzero high
 * limb, canonicalizes negative zero, and signed comparison agrees with the
 * represented mathematical integer for every input encoding.
 *****************************************************************************)
Theory compute_boundedSignedEndpoint
Ancestors
  compute_boundedSignedAdd compute_boundedSigned compute_bounded
  arithmetic words integer
Libs
  bossLib intLib

val _ = numLib.temp_prefer_num ();

Definition bounded_signed64_make_def:
  bounded_signed64_make negative magnitude =
    BoundedSigned64 (negative ∧ magnitude ≠ 0w) magnitude
End

Definition bounded_signed64_normalized_def:
  bounded_signed64_normalized (BoundedSigned64 negative magnitude) ⇔
    ¬negative ∨ magnitude ≠ 0w
End

Definition bounded_signed64_to_int_def:
  bounded_signed64_to_int (BoundedSigned64 negative magnitude) =
    if negative then -&(w2n magnitude) else &(w2n magnitude)
End

Definition bounded_signed128_to_int_def:
  bounded_signed128_to_int (BoundedSigned128 negative magnitude) =
    if negative then -&(bounded128_to_num magnitude)
    else &(bounded128_to_num magnitude)
End

Definition bounded_signed64_widen128_def:
  bounded_signed64_widen128 (BoundedSigned64 negative magnitude) =
    bounded_signed128_make negative (Bounded128 0w magnitude)
End

Definition bounded_signed128_narrow64_def:
  bounded_signed128_narrow64
      (BoundedSigned128 negative (Bounded128 high low)) =
    if high = 0w then SOME (bounded_signed64_make negative low)
    else NONE
End

Definition bounded_signed64_effective_negative_def:
  bounded_signed64_effective_negative
      (BoundedSigned64 negative magnitude) =
    (negative ∧ magnitude ≠ 0w)
End

Definition bounded_signed64_magnitude_def:
  bounded_signed64_magnitude (BoundedSigned64 negative magnitude) = magnitude
End

Definition bounded_signed64_le_def:
  bounded_signed64_le left right =
    let left_negative = bounded_signed64_effective_negative left in
    let right_negative = bounded_signed64_effective_negative right in
    let left_magnitude = bounded_signed64_magnitude left in
    let right_magnitude = bounded_signed64_magnitude right in
    if left_negative then
      if right_negative then ¬word_lo left_magnitude right_magnitude
      else T
    else if right_negative then F
    else ¬word_lo right_magnitude left_magnitude
End

Definition bounded_signed64_min_def:
  bounded_signed64_min left right =
    if bounded_signed64_le left right then left else right
End

Definition bounded_signed64_max_def:
  bounded_signed64_max left right =
    if bounded_signed64_le left right then right else left
End

Theorem bounded_signed64_make_normalized:
  bounded_signed64_normalized
    (bounded_signed64_make negative magnitude)
Proof
  Cases_on `negative`
  >> simp [bounded_signed64_make_def, bounded_signed64_normalized_def]
QED

Theorem bounded_signed64_make_value:
  bounded_signed64_to_int
    (bounded_signed64_make negative magnitude) =
  (if negative then -&(w2n magnitude) else &(w2n magnitude))
Proof
  Cases_on `negative`
  >> Cases_on `magnitude = 0w`
  >> simp [bounded_signed64_make_def, bounded_signed64_to_int_def,
           wordsTheory.w2n_eq_0]
QED

Theorem bounded_signed64_widen128_normalized:
  bounded_signed128_normalized (bounded_signed64_widen128 value)
Proof
  Cases_on `value`
  >> simp [bounded_signed64_widen128_def,
           bounded_signed128_make_normalized]
QED

Theorem bounded_signed64_widen128_value:
  bounded_signed128_to_int (bounded_signed64_widen128 value) =
  bounded_signed64_to_int value
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `magnitude = 0w`
  >> simp [bounded_signed64_widen128_def,
           bounded_signed128_make_def, bounded_signed128_to_int_def,
           bounded_signed64_to_int_def, bounded128_is_zero_def,
           bounded128_to_num_def, wordsTheory.w2n_eq_0]
QED

Theorem bounded_signed128_narrow64_none:
  bounded_signed128_narrow64
    (BoundedSigned128 negative (Bounded128 high low)) = NONE ⇔
  high ≠ 0w
Proof
  simp [bounded_signed128_narrow64_def]
QED

Theorem bounded_signed128_narrow64_some:
  bounded_signed128_narrow64 source = SOME result ⇒
  bounded_signed64_normalized result ∧
  bounded_signed64_to_int result = bounded_signed128_to_int source
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned128 negative magnitude`
  >> Cases_on `magnitude`
  >> rename1 `Bounded128 high low`
  >> rw [bounded_signed128_narrow64_def]
  >- simp [bounded_signed64_make_normalized]
  >> Cases_on `negative`
  >> Cases_on `low = 0w`
  >> simp [bounded_signed64_make_value,
           bounded_signed128_to_int_def, bounded128_to_num_def,
           wordsTheory.w2n_eq_0]
QED

Theorem bounded_endpoint_digit_threshold:
  0 < base ∧ low < base ⇒
  (base ≤ low + base * high ⇔ 0 < high)
Proof
  strip_tac
  >> Cases_on `high`
  >> simp [MULT_SUC]
QED

Theorem bounded_signed128_narrow64_overflow_iff:
  bounded_signed128_narrow64
    (BoundedSigned128 negative magnitude) = NONE ⇔
  bounded_word_base ≤ bounded128_to_num magnitude
Proof
  Cases_on `magnitude`
  >> rw [bounded_signed128_narrow64_def, bounded128_to_num_def]
  >> `0 < bounded_word_base` by simp [bounded_word_base_positive]
  >> `w2n (c0:word64) < bounded_word_base` by
       (qspec_then `c0` assume_tac w2n_lt
        >> fs [bounded_word_base_def])
  >> `bounded_word_base ≤
        w2n c0 + bounded_word_base * w2n c ⇔ 0 < w2n c` by
       metis_tac
         [Q.INST [`base` |-> `bounded_word_base`,
                  `low` |-> `w2n (c0:word64)`,
                  `high` |-> `w2n (c:word64)`]
            bounded_endpoint_digit_threshold]
  >> `c ≠ 0w ⇔ w2n c ≠ 0` by
       metis_tac [Q.SPEC `c` wordsTheory.w2n_eq_0]
  >> `w2n c ≠ 0 ⇔ 0 < w2n c` by
       (Cases_on `w2n c` >> simp [])
  >> metis_tac []
QED

Theorem bounded_signed64_le_correct:
  bounded_signed64_le left right ⇔
  bounded_signed64_to_int left ≤ bounded_signed64_to_int right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `c`
  >> Cases_on `c'`
  >> rw [bounded_signed64_le_def, LET_THM,
         bounded_signed64_effective_negative_def,
         bounded_signed64_magnitude_def, bounded_signed64_to_int_def,
         WORD_LO, wordsTheory.w2n_eq_0]
  >> qspec_then `c0` assume_tac w2n_lt
  >> qspec_then `c0'` assume_tac w2n_lt
  >> fs [dimword_64]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_min_correct:
  bounded_signed64_to_int (bounded_signed64_min left right) =
  (if bounded_signed64_to_int left ≤ bounded_signed64_to_int right then
     bounded_signed64_to_int left
   else bounded_signed64_to_int right)
Proof
  rw [bounded_signed64_min_def, bounded_signed64_le_correct]
  >> Cases_on
       `bounded_signed64_to_int left ≤ bounded_signed64_to_int right`
  >> simp []
QED

Theorem bounded_signed64_max_correct:
  bounded_signed64_to_int (bounded_signed64_max left right) =
  (if bounded_signed64_to_int left ≤ bounded_signed64_to_int right then
     bounded_signed64_to_int right
   else bounded_signed64_to_int left)
Proof
  rw [bounded_signed64_max_def, bounded_signed64_le_correct]
  >> Cases_on
       `bounded_signed64_to_int left ≤ bounded_signed64_to_int right`
  >> simp []
QED

Theorem bounded_signed_endpoint_closed_tests:
  bounded_signed128_narrow64
    (BoundedSigned128 T (Bounded128 0w 0w)) =
      SOME (BoundedSigned64 F 0w) ∧
  bounded_signed128_narrow64
    (BoundedSigned128 F (Bounded128 1w 0w)) = NONE ∧
  bounded_signed64_le (BoundedSigned64 T 7w)
    (BoundedSigned64 T 5w) ∧
  ¬bounded_signed64_le (BoundedSigned64 F 7w)
    (BoundedSigned64 F 5w) ∧
  bounded_signed64_le (BoundedSigned64 T 0w)
    (BoundedSigned64 F 0w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
