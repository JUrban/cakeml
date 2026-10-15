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
