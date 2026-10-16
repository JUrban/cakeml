(*****************************************************************************
 * Canonical decimal reciprocal certificates for object-checker refinement.
 *
 * The specialized checker previously accepted any outward reciprocal
 * enclosure.  The authenticated historical object program instead computes
 * one deterministic enclosure with floor/ceiling division by the positive
 * input endpoints.  Sound enclosure is not enough for exact refinement, so
 * this theory exposes the object's operation and an executable stronger
 * certificate requiring the supplied interval to be that canonical result.
 *****************************************************************************)
Theory compute_boundedObjectCertificateDecimal
Ancestors
  compute_boundedObjectDecimalArithmetic compute_boundedCertificateDecimal
Libs
  bossLib preamble

Definition bounded_object_fs_hist_positive_inv_def:
  bounded_object_fs_hist_positive_inv
      (Pair (Pair (Num lower) (Num 0))
        (Pair (Num upper) (Num 0)) : cv) =
    (case bounded_object_fs_floor_div
       (Pair (Num 1000000000000000000000000) (Num 0)) upper of
     | NONE => NONE
     | SOME result_lower =>
       case bounded_object_fs_ceil_div
         (Pair (Num 1000000000000000000000000) (Num 0)) lower of
       | NONE => NONE
       | SOME result_upper => SOME (Pair result_lower result_upper)) /\
  bounded_object_fs_hist_positive_inv _ = NONE
End

Definition bounded_interval64_positive_inv_certificate_decimal_def:
  bounded_interval64_positive_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) <=>
    bounded_interval64_inv_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
    bounded_signed64_strict_positive input_lower /\
    w2n (bounded_signed64_magnitude output_lower) =
      1000000000000000000000000 DIV
        w2n (bounded_signed64_magnitude input_upper) /\
    w2n (bounded_signed64_magnitude output_upper) =
      1000000000000000000000000 DIV
        w2n (bounded_signed64_magnitude input_lower) +
      if 1000000000000000000000000 MOD
           w2n (bounded_signed64_magnitude input_lower) = 0
      then 0 else 1
End

Definition bounded_object_fs_hist_positive_root_certificate_def:
  bounded_object_fs_hist_positive_root_certificate
      (Pair (Pair (Num input_lower) (Num 0))
        (Pair (Num input_upper) (Num 0)) : cv)
      (Pair (Pair (Num root_lower) (Num 0))
        (Pair (Num root_upper) (Num 0)) : cv) =
    Num
      (if 0 < input_lower /\ input_lower <= input_upper /\
          0 < root_lower /\ root_lower <= root_upper /\
          root_lower * root_lower <= input_lower * 1000000000000 /\
          input_upper * 1000000000000 <= root_upper * root_upper
       then 1 else 0) /\
  bounded_object_fs_hist_positive_root_certificate _ _ = Num 0
End

Definition bounded_interval64_positive_sqrt_certificate_decimal_def:
  bounded_interval64_positive_sqrt_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) <=>
    bounded_interval64_sqrt_certificate_decimal
      (BoundedInterval64 input_lower input_upper)
      (BoundedInterval64 output_lower output_upper) /\
    bounded_signed64_strict_positive input_lower /\
    bounded_signed64_strict_positive output_lower
End

Theorem bounded_interval64_positive_inv_certificate_decimal_sound:
  bounded_interval64_positive_inv_certificate_decimal input output ==>
  bounded_interval64_inv_certificate_decimal input output
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp [bounded_interval64_positive_inv_certificate_decimal_def]
QED

Theorem bounded_interval64_positive_inv_certificate_decimal_object_exact:
  bounded_interval64_positive_inv_certificate_decimal input output ==>
  bounded_object_fs_hist_positive_inv
    (bounded_interval64_object_cv input) =
    SOME (bounded_interval64_object_cv output)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> fs [bounded_interval64_positive_inv_certificate_decimal_def]
  >> imp_res_tac
       bounded_interval64_inv_certificate_decimal_positive_signs
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b0'`
  >> gvs [bounded_object_fs_hist_positive_inv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
          compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
          compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
          bounded_object_fs_floor_div_def,
          bounded_object_fs_ceil_div_def,
          bounded_object_q_ceil_div_def]
QED

Theorem bounded_interval64_positive_sqrt_certificate_decimal_sound:
  bounded_interval64_positive_sqrt_certificate_decimal input output ==>
  bounded_interval64_sqrt_certificate_decimal input output
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp [bounded_interval64_positive_sqrt_certificate_decimal_def]
QED

Theorem bounded_interval64_positive_sqrt_certificate_decimal_object_exact:
  bounded_interval64_positive_sqrt_certificate_decimal input output ==>
  bounded_object_fs_hist_positive_root_certificate
    (bounded_interval64_object_cv input)
    (bounded_interval64_object_cv output) = Num 1
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> fs [bounded_interval64_positive_sqrt_certificate_decimal_def]
  >> imp_res_tac
       bounded_interval64_sqrt_certificate_decimal_magnitude_bounds
  >> imp_res_tac
       bounded_interval64_sqrt_certificate_decimal_nonnegative
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b0'`
  >> gvs [bounded_object_fs_hist_positive_root_certificate_def,
          compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
          compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
          compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
          compute_boundedIntervalTheory.bounded_interval64_valid_def,
          compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
          compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> gvs [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
          wordsTheory.w2n_eq_0]
QED

Theorem bounded_interval64_positive_inv_certificate_decimal_closed_tests:
  let input = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 4000000000000w) in
  let output = BoundedInterval64
    (BoundedSigned64 F 250000000000w)
    (BoundedSigned64 F 500000000000w) in
  let wider = BoundedInterval64
    (BoundedSigned64 F 249999999999w)
    (BoundedSigned64 F 500000000001w) in
  bounded_interval64_positive_inv_certificate_decimal input output /\
  bounded_interval64_inv_certificate_decimal input wider /\
  ~bounded_interval64_positive_inv_certificate_decimal input wider
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_interval64_positive_sqrt_certificate_decimal_closed_tests:
  let input = BoundedInterval64
    (BoundedSigned64 F 4000000000000w)
    (BoundedSigned64 F 4000000000000w) in
  let output = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 2000000000000w) in
  let zero = BoundedInterval64
    (BoundedSigned64 F 0w) (BoundedSigned64 F 0w) in
  bounded_interval64_positive_sqrt_certificate_decimal input output /\
  bounded_interval64_sqrt_certificate_decimal zero zero /\
  ~bounded_interval64_positive_sqrt_certificate_decimal zero zero
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
