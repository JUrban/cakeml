(*****************************************************************************
 * Checked fixed-scale square-root certificates.
 *
 * Square roots are supplied as reusable external data.  Candle authenticates
 * them by exact word products: lower^2 <= input_lower * 2^40 and
 * input_upper * 2^40 <= upper^2.  No numerical square-root algorithm or
 * per-leaf proof construction is required inside the hot path.
 *****************************************************************************)
Theory compute_boundedSqrtCertificate
Ancestors
  compute_boundedTaylorGradient
Libs
  bossLib preamble

Definition bounded_interval64_sqrt_certificate_def:
  bounded_interval64_sqrt_certificate
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) =
    (bounded_interval64_valid
       (BoundedInterval64 input_lower input_upper) ∧
     bounded_interval64_valid
       (BoundedInterval64 output_lower output_upper) ∧
     bounded_signed64_nonnegative input_lower ∧
     bounded_signed64_nonnegative output_lower ∧
     let input_lower_scaled = bounded_word64_product128
       (bounded_signed64_magnitude input_lower) 1099511627776w in
     let input_upper_scaled = bounded_word64_product128
       (bounded_signed64_magnitude input_upper) 1099511627776w in
     let output_lower_squared = bounded_word64_product128
       (bounded_signed64_magnitude output_lower)
       (bounded_signed64_magnitude output_lower) in
     let output_upper_squared = bounded_word64_product128
       (bounded_signed64_magnitude output_upper)
       (bounded_signed64_magnitude output_upper) in
     bounded128_le_words output_lower_squared input_lower_scaled ∧
     bounded128_le_words input_upper_scaled output_upper_squared)
End

Theorem bounded_interval64_sqrt_certificate_closed_tests:
  let input = BoundedInterval64
    (BoundedSigned64 F 4398046511104w)
    (BoundedSigned64 F 4398046511104w) in
  let exact_output = BoundedInterval64
    (BoundedSigned64 F 2199023255552w)
    (BoundedSigned64 F 2199023255552w) in
  let short_output = BoundedInterval64
    (BoundedSigned64 F 2199023255551w)
    (BoundedSigned64 F 2199023255551w) in
  let negative_input = BoundedInterval64
    (BoundedSigned64 T 1w) (BoundedSigned64 F 1w) in
  bounded_interval64_sqrt_certificate input exact_output ∧
  ¬bounded_interval64_sqrt_certificate input short_output ∧
  ¬bounded_interval64_sqrt_certificate negative_input exact_output
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
