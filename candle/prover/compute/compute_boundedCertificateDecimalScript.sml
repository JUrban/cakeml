(*****************************************************************************
 * Checked decimal fixed-scale square-root and reciprocal certificates.
 *
 * The established fast checker uses the same sign/magnitude carrier at
 * scale 2^40.  These definitions retain its exact word-product checks while
 * matching the authenticated HOL Light object's scale 10^12.  Certificate
 * preparation remains untrusted: acceptance checks every endpoint product.
 *****************************************************************************)
Theory compute_boundedCertificateDecimal
Ancestors
  compute_boundedReciprocalCertificate compute_boundedIntervalDecimal
Libs
  bossLib preamble

Definition bounded_decimal_scale_squared128_def:
  bounded_decimal_scale_squared128 =
    Bounded128 54210w 2003764205206896640w
End

Theorem bounded_decimal_scale_squared128_value:
  bounded128_to_num bounded_decimal_scale_squared128 =
    1000000000000000000000000
Proof
  rw [bounded_decimal_scale_squared128_def,
      compute_boundedTheory.bounded128_to_num_def,
      compute_boundedTheory.bounded_word_base_def]
QED

Definition bounded_interval64_sqrt_certificate_decimal_def:
  bounded_interval64_sqrt_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) =
    (bounded_interval64_valid
       (BoundedInterval64 input_lower input_upper) /\
     bounded_interval64_valid
       (BoundedInterval64 output_lower output_upper) /\
     bounded_signed64_nonnegative input_lower /\
     bounded_signed64_nonnegative output_lower /\
     let input_lower_scaled = bounded_word64_product128
       (bounded_signed64_magnitude input_lower) 1000000000000w in
     let input_upper_scaled = bounded_word64_product128
       (bounded_signed64_magnitude input_upper) 1000000000000w in
     let output_lower_squared = bounded_word64_product128
       (bounded_signed64_magnitude output_lower)
       (bounded_signed64_magnitude output_lower) in
     let output_upper_squared = bounded_word64_product128
       (bounded_signed64_magnitude output_upper)
       (bounded_signed64_magnitude output_upper) in
     bounded128_le_words output_lower_squared input_lower_scaled /\
     bounded128_le_words input_upper_scaled output_upper_squared)
End

Theorem bounded_interval64_sqrt_certificate_decimal_magnitude_bounds:
  bounded_interval64_sqrt_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) ==>
  w2n (bounded_signed64_magnitude output_lower) *
      w2n (bounded_signed64_magnitude output_lower) <=
    w2n (bounded_signed64_magnitude input_lower) * 1000000000000 /\
  w2n (bounded_signed64_magnitude input_upper) * 1000000000000 <=
    w2n (bounded_signed64_magnitude output_upper) *
      w2n (bounded_signed64_magnitude output_upper)
Proof
  rw [bounded_interval64_sqrt_certificate_decimal_def, LET_THM,
      compute_boundedSignedAddTheory.bounded128_le_words_correct,
      compute_boundedTaylorCompleteTheory.bounded_word64_product128_value]
QED

Theorem bounded_interval64_sqrt_certificate_decimal_nonnegative:
  bounded_interval64_sqrt_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) ==>
  bounded_interval64_valid
      (BoundedInterval64 input_lower input_upper) /\
  bounded_interval64_valid
      (BoundedInterval64 output_lower output_upper) /\
  bounded_signed64_nonnegative input_lower /\
  bounded_signed64_nonnegative input_upper /\
  bounded_signed64_nonnegative output_lower /\
  bounded_signed64_nonnegative output_upper
Proof
  strip_tac
  >> fs [bounded_interval64_sqrt_certificate_decimal_def,
         compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
         compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_sqrt_certificate_decimal_int_bounds:
  bounded_interval64_sqrt_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) ==>
  bounded_signed64_to_int output_lower *
      bounded_signed64_to_int output_lower <=
    (&1000000000000:int) * bounded_signed64_to_int input_lower /\
  (&1000000000000:int) * bounded_signed64_to_int input_upper <=
    bounded_signed64_to_int output_upper *
      bounded_signed64_to_int output_upper
Proof
  strip_tac
  >> imp_res_tac
       bounded_interval64_sqrt_certificate_decimal_magnitude_bounds
  >> imp_res_tac bounded_interval64_sqrt_certificate_decimal_nonnegative
  >> fs [compute_boundedIntervalTheory.bounded_signed64_nonnegative_magnitude_value,
         integerTheory.INT_OF_NUM_MUL,
         integerTheory.INT_OF_NUM_LE]
QED

Theorem bounded_interval64_sqrt_certificate_decimal_contains_scaled_square:
  bounded_interval64_contains_scaled_int input
      (&1000000000000000000000000:int) exact_value /\
  bounded_interval64_sqrt_certificate_decimal input output ==>
  (&1000000000000:int) *
      bounded_signed64_to_int (bounded_interval64_lower output) *
      bounded_signed64_to_int (bounded_interval64_lower output) <=
    exact_value /\
  exact_value <=
    (&1000000000000:int) *
      bounded_signed64_to_int (bounded_interval64_upper output) *
      bounded_signed64_to_int (bounded_interval64_upper output)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> imp_res_tac bounded_interval64_sqrt_certificate_decimal_int_bounds
  >> fs [compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> intLib.ARITH_TAC
QED

Definition bounded_interval64_inv_certificate_decimal_def:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) =
    (bounded_interval64_valid
       (BoundedInterval64 input_lower input_upper) /\
     bounded_interval64_valid
       (BoundedInterval64 output_lower output_upper) /\
     if bounded_signed64_strict_positive input_lower then
       bounded_signed64_strict_positive output_lower /\
       let lower_product = bounded_word64_product128
         (bounded_signed64_magnitude output_lower)
         (bounded_signed64_magnitude input_upper) in
       let upper_product = bounded_word64_product128
         (bounded_signed64_magnitude output_upper)
         (bounded_signed64_magnitude input_lower) in
       bounded128_le_words lower_product
         bounded_decimal_scale_squared128 /\
       bounded128_le_words bounded_decimal_scale_squared128
         upper_product
     else if bounded_signed64_strict_negative input_upper then
       bounded_signed64_strict_negative output_upper /\
       let lower_product = bounded_word64_product128
         (bounded_signed64_magnitude output_lower)
         (bounded_signed64_magnitude input_upper) in
       let upper_product = bounded_word64_product128
         (bounded_signed64_magnitude output_upper)
         (bounded_signed64_magnitude input_lower) in
       bounded128_le_words bounded_decimal_scale_squared128
         lower_product /\
       bounded128_le_words upper_product
         bounded_decimal_scale_squared128
     else F)
End

Theorem bounded_interval64_inv_certificate_decimal_positive_magnitude_bounds:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
  bounded_signed64_strict_positive input_lower ==>
  bounded_signed64_strict_positive output_lower /\
  w2n (bounded_signed64_magnitude output_lower) *
      w2n (bounded_signed64_magnitude input_upper) <=
    1000000000000000000000000 /\
  1000000000000000000000000 <=
    w2n (bounded_signed64_magnitude output_upper) *
      w2n (bounded_signed64_magnitude input_lower)
Proof
  rw [bounded_interval64_inv_certificate_decimal_def, LET_THM,
      compute_boundedSignedAddTheory.bounded128_le_words_correct,
      compute_boundedTaylorCompleteTheory.bounded_word64_product128_value,
      bounded_decimal_scale_squared128_value]
QED

Theorem bounded_interval64_inv_certificate_decimal_negative_magnitude_bounds:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
  ~bounded_signed64_strict_positive input_lower /\
  bounded_signed64_strict_negative input_upper ==>
  bounded_signed64_strict_negative output_upper /\
  1000000000000000000000000 <=
    w2n (bounded_signed64_magnitude output_lower) *
      w2n (bounded_signed64_magnitude input_upper) /\
  w2n (bounded_signed64_magnitude output_upper) *
      w2n (bounded_signed64_magnitude input_lower) <=
    1000000000000000000000000
Proof
  rw [bounded_interval64_inv_certificate_decimal_def, LET_THM,
      compute_boundedSignedAddTheory.bounded128_le_words_correct,
      compute_boundedTaylorCompleteTheory.bounded_word64_product128_value,
      bounded_decimal_scale_squared128_value]
QED

Theorem bounded_interval64_inv_certificate_decimal_positive_signs:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
  bounded_signed64_strict_positive input_lower ==>
  bounded_signed64_strict_positive input_upper /\
  bounded_signed64_strict_positive output_lower /\
  bounded_signed64_strict_positive output_upper
Proof
  strip_tac
  >> fs [bounded_interval64_inv_certificate_decimal_def,
         compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
         compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_inv_certificate_decimal_positive_int_bounds:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
  bounded_signed64_strict_positive input_lower ==>
  bounded_signed64_to_int output_lower *
      bounded_signed64_to_int input_upper <=
    (&1000000000000000000000000:int) /\
  (&1000000000000000000000000:int) <=
    bounded_signed64_to_int output_upper *
      bounded_signed64_to_int input_lower
Proof
  strip_tac
  >> imp_res_tac
       bounded_interval64_inv_certificate_decimal_positive_magnitude_bounds
  >> imp_res_tac bounded_interval64_inv_certificate_decimal_positive_signs
  >> fs [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
         compute_boundedIntervalTheory.bounded_signed64_nonnegative_magnitude_value,
         integerTheory.INT_OF_NUM_MUL,
         integerTheory.INT_OF_NUM_LE]
QED

Theorem bounded_interval64_inv_certificate_decimal_negative_signs:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
  bounded_signed64_strict_negative input_upper ==>
  bounded_signed64_strict_negative input_lower /\
  bounded_signed64_strict_negative output_lower /\
  bounded_signed64_strict_negative output_upper
Proof
  strip_tac
  >> fs [bounded_interval64_inv_certificate_decimal_def,
         compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
         compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct,
         compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_inv_certificate_decimal_negative_int_bounds:
  bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
  bounded_signed64_strict_negative input_upper ==>
  (&1000000000000000000000000:int) <=
    bounded_signed64_to_int output_lower *
      bounded_signed64_to_int input_upper /\
  bounded_signed64_to_int output_upper *
      bounded_signed64_to_int input_lower <=
    (&1000000000000000000000000:int)
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_inv_certificate_decimal_negative_signs
  >> `~bounded_signed64_strict_positive input_lower` by
       fs [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
           compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
           compute_boundedIntervalTheory.bounded_signed64_nonnegative_def]
  >> imp_res_tac
       bounded_interval64_inv_certificate_decimal_negative_magnitude_bounds
  >> fs [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
         compute_boundedIntervalTheory.bounded_signed64_effective_negative_magnitude_value,
         integerTheory.INT_MUL_CALCULATE,
         integerTheory.INT_OF_NUM_MUL,
         integerTheory.INT_OF_NUM_LE]
QED

Theorem bounded_interval64_sqrt_certificate_decimal_closed_tests:
  let input = BoundedInterval64
    (BoundedSigned64 F 4000000000000w)
    (BoundedSigned64 F 4000000000000w) in
  let exact_output = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 2000000000000w) in
  let short_output = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 1999999999999w) in
  let negative_input = BoundedInterval64
    (BoundedSigned64 T 1w) (BoundedSigned64 F 1w) in
  bounded_interval64_sqrt_certificate_decimal input exact_output /\
  ~bounded_interval64_sqrt_certificate_decimal input short_output /\
  ~bounded_interval64_sqrt_certificate_decimal negative_input exact_output
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_inv_certificate_decimal_closed_tests:
  let positive_input = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 4000000000000w) in
  let positive_output = BoundedInterval64
    (BoundedSigned64 F 250000000000w)
    (BoundedSigned64 F 500000000000w) in
  let positive_short = BoundedInterval64
    (BoundedSigned64 F 250000000001w)
    (BoundedSigned64 F 499999999999w) in
  let negative_input = BoundedInterval64
    (BoundedSigned64 T 4000000000000w)
    (BoundedSigned64 T 2000000000000w) in
  let negative_output = BoundedInterval64
    (BoundedSigned64 T 500000000000w)
    (BoundedSigned64 T 250000000000w) in
  let crossing_input = BoundedInterval64
    (BoundedSigned64 T 1w) (BoundedSigned64 F 1w) in
  bounded_interval64_inv_certificate_decimal
    positive_input positive_output /\
  ~bounded_interval64_inv_certificate_decimal
    positive_input positive_short /\
  bounded_interval64_inv_certificate_decimal
    negative_input negative_output /\
  ~bounded_interval64_inv_certificate_decimal
    crossing_input positive_output
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
