(*****************************************************************************
 * Checked fixed-scale reciprocal certificates.
 *
 * External preparation supplies an outward reciprocal interval.  For a
 * valid sign-stable input, reciprocal monotonicity reduces containment to
 * two exact endpoint-product comparisons against 2^80.  This avoids a word
 * long-division loop in the recurring checker while keeping preparation
 * untrusted and explicitly checked.
 *****************************************************************************)
Theory compute_boundedReciprocalCertificate
Ancestors
  compute_boundedSqrtCertificate
Libs
  bossLib preamble

Definition bounded_signed64_strict_positive_def:
  bounded_signed64_strict_positive value =
    (bounded_signed64_nonnegative value ∧
     bounded_signed64_magnitude value ≠ 0w)
End

Definition bounded_signed64_strict_negative_def:
  bounded_signed64_strict_negative value =
    bounded_signed64_effective_negative value
End

Definition bounded_scale_squared128_def:
  bounded_scale_squared128 = Bounded128 65536w 0w
End

Theorem bounded_scale_squared128_value:
  bounded128_to_num bounded_scale_squared128 =
    1208925819614629174706176
Proof
  rw [bounded_scale_squared128_def,
      compute_boundedTheory.bounded128_to_num_def,
      compute_boundedTheory.bounded_word_base_def]
QED

Definition bounded_interval64_inv_certificate_def:
  bounded_interval64_inv_certificate
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) =
    (bounded_interval64_valid
       (BoundedInterval64 input_lower input_upper) ∧
     bounded_interval64_valid
       (BoundedInterval64 output_lower output_upper) ∧
     if bounded_signed64_strict_positive input_lower then
       bounded_signed64_strict_positive output_lower ∧
       let lower_product = bounded_word64_product128
         (bounded_signed64_magnitude output_lower)
         (bounded_signed64_magnitude input_upper) in
       let upper_product = bounded_word64_product128
         (bounded_signed64_magnitude output_upper)
         (bounded_signed64_magnitude input_lower) in
       bounded128_le_words lower_product bounded_scale_squared128 ∧
       bounded128_le_words bounded_scale_squared128 upper_product
     else if bounded_signed64_strict_negative input_upper then
       bounded_signed64_strict_negative output_upper ∧
       let lower_product = bounded_word64_product128
         (bounded_signed64_magnitude output_lower)
         (bounded_signed64_magnitude input_upper) in
       let upper_product = bounded_word64_product128
         (bounded_signed64_magnitude output_upper)
         (bounded_signed64_magnitude input_lower) in
       bounded128_le_words bounded_scale_squared128 lower_product ∧
       bounded128_le_words upper_product bounded_scale_squared128
     else F)
End

Theorem bounded_interval64_inv_certificate_positive_magnitude_bounds:
  bounded_interval64_inv_certificate
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) ∧
  bounded_signed64_strict_positive input_lower ⇒
  bounded_signed64_strict_positive output_lower ∧
  w2n (bounded_signed64_magnitude output_lower) *
      w2n (bounded_signed64_magnitude input_upper) ≤
    1208925819614629174706176 ∧
  1208925819614629174706176 ≤
    w2n (bounded_signed64_magnitude output_upper) *
      w2n (bounded_signed64_magnitude input_lower)
Proof
  rw [bounded_interval64_inv_certificate_def, LET_THM,
      compute_boundedSignedAddTheory.bounded128_le_words_correct,
      compute_boundedTaylorCompleteTheory.bounded_word64_product128_value,
      bounded_scale_squared128_value]
QED

Theorem bounded_interval64_inv_certificate_negative_magnitude_bounds:
  bounded_interval64_inv_certificate
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) ∧
  ¬bounded_signed64_strict_positive input_lower ∧
  bounded_signed64_strict_negative input_upper ⇒
  bounded_signed64_strict_negative output_upper ∧
  1208925819614629174706176 ≤
    w2n (bounded_signed64_magnitude output_lower) *
      w2n (bounded_signed64_magnitude input_upper) ∧
  w2n (bounded_signed64_magnitude output_upper) *
      w2n (bounded_signed64_magnitude input_lower) ≤
    1208925819614629174706176
Proof
  rw [bounded_interval64_inv_certificate_def, LET_THM,
      compute_boundedSignedAddTheory.bounded128_le_words_correct,
      compute_boundedTaylorCompleteTheory.bounded_word64_product128_value,
      bounded_scale_squared128_value]
QED

Theorem bounded_interval64_inv_certificate_closed_tests:
  let positive_input = BoundedInterval64
    (BoundedSigned64 F 2199023255552w)
    (BoundedSigned64 F 4398046511104w) in
  let positive_output = BoundedInterval64
    (BoundedSigned64 F 274877906944w)
    (BoundedSigned64 F 549755813888w) in
  let positive_short = BoundedInterval64
    (BoundedSigned64 F 274877906945w)
    (BoundedSigned64 F 549755813887w) in
  let negative_input = BoundedInterval64
    (BoundedSigned64 T 4398046511104w)
    (BoundedSigned64 T 2199023255552w) in
  let negative_output = BoundedInterval64
    (BoundedSigned64 T 549755813888w)
    (BoundedSigned64 T 274877906944w) in
  let crossing_input = BoundedInterval64
    (BoundedSigned64 T 1w) (BoundedSigned64 F 1w) in
  bounded_interval64_inv_certificate positive_input positive_output ∧
  ¬bounded_interval64_inv_certificate positive_input positive_short ∧
  bounded_interval64_inv_certificate negative_input negative_output ∧
  ¬bounded_interval64_inv_certificate crossing_input positive_output
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
