(*****************************************************************************
 * Typed decimal bindings for the rational operations used by source sqrt.
 *
 * These lemmas connect exact fixed-scale addition and the canonical decimal
 * reciprocal certificate to the representation-independent rational
 * relation.  They contain no closed case-10173 data.
 *****************************************************************************)
Theory compute_boundedCase10173SourceDerivativeBinding
Ancestors
  compute_boundedCase10173SourceDecimalExact
  compute_boundedQRelationAlgebra
  compute_boundedObjectCertificateDecimal
Libs
  bossLib preamble wordsLib intLib

Theorem bounded_case10173_positive_interval64_self_add_magnitudes:
  bounded_interval64_add
      (BoundedInterval64 (BoundedSigned64 F lower)
        (BoundedSigned64 F upper))
      (BoundedInterval64 (BoundedSigned64 F lower)
        (BoundedSigned64 F upper)) =
    SOME
      (BoundedInterval64 (BoundedSigned64 F twice_lower)
        (BoundedSigned64 F twice_upper)) ==>
  w2n twice_lower = w2n lower + w2n lower /\
  w2n twice_upper = w2n upper + w2n upper
Proof
  strip_tac
  >> drule
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> simp
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> strip_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case10173_positive_q_self_add_endpoint_equiv:
  bounded_signed64_strict_positive (BoundedSigned64 F magnitude) /\
  w2n twice_magnitude = w2n magnitude + w2n magnitude ==>
  bounded_case10173_q_cv_equiv
    (Pair
      (Pair
        (Num
          (w2n magnitude * 1000000000000 +
           w2n magnitude * 1000000000000))
        (Num 0))
      (Num (1000000000000 * 1000000000000 - 1)))
    (bounded_case10173_positive_endpoint64_q_cv
      (BoundedSigned64 F twice_magnitude))
Proof
  strip_tac
  >> fs
    [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
     compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
     compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
     integerTheory.INT_MUL]
  >> INT_RING_TAC
QED

Theorem bounded_case10173_positive_inv_certificate_q_conversion:
  bounded_interval64_positive_inv_certificate_decimal
    (BoundedInterval64 (BoundedSigned64 F input_lower)
      (BoundedSigned64 F input_upper))
    (BoundedInterval64 (BoundedSigned64 F output_lower)
      (BoundedSigned64 F output_upper)) ==>
  bounded_object_positive_q_interval64_decimal
    (Pair
      (Pair (Pair (Num 1000000000000) (Num 0))
        (Num (w2n input_upper - 1)))
      (Pair (Pair (Num 1000000000000) (Num 0))
        (Num (w2n input_lower - 1)))) =
    SOME
      (BoundedInterval64 (BoundedSigned64 F output_lower)
        (BoundedSigned64 F output_upper))
Proof
  strip_tac
  >> drule
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_object_exact
  >> strip_tac
  >> fs
    [compute_boundedObjectCertificateDecimalTheory.bounded_object_fs_hist_positive_inv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
     compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
     compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
     compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_def]
  >> `bounded_interval64_inv_certificate_decimal
        (BoundedInterval64 (BoundedSigned64 F input_lower)
          (BoundedSigned64 F input_upper))
        (BoundedInterval64 (BoundedSigned64 F output_lower)
          (BoundedSigned64 F output_upper)) /\
      bounded_signed64_strict_positive
        (BoundedSigned64 F input_lower)` by
       fs
         [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_def]
  >> imp_res_tac
       compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_positive_signs
  >> qspec_then `output_lower` assume_tac wordsTheory.w2n_lt
  >> qspec_then `output_upper` assume_tac wordsTheory.w2n_lt
  >> fs [compute_boundedTheory.bounded_word_base_def]
  >> `input_lower <> 0w /\ input_upper <> 0w` by
       fs
         [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
  >> `w2n input_lower <> 0 /\ w2n input_upper <> 0` by
       metis_tac [wordsTheory.w2n_eq_0]
  >> `0 < w2n input_lower /\ 0 < w2n input_upper` by
       intLib.ARITH_TAC
  >> `SUC (w2n input_lower - 1) = w2n input_lower /\
      SUC (w2n input_upper - 1) = w2n input_upper` by
       intLib.ARITH_TAC
  >> `bounded_interval64_valid
        (BoundedInterval64 (BoundedSigned64 F output_lower)
          (BoundedSigned64 F output_upper))` by
       fs
         [compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_def]
  >> fs
    [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
     compute_boundedTheory.bounded_word_base_eq,
     compute_boundedSignedTheory.bounded_div_ceil,
     wordsTheory.n2w_w2n]
QED

val _ = export_theory ();
