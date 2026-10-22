(*****************************************************************************
 * Registered source first derivative on an authenticated exact sqrt root.
 *
 * The source keeps the root certificate as a rational interval, while the
 * decimal checker authenticates its exact 10^12 representation and the
 * reciprocal of twice that interval.  This theorem joins those views for an
 * arbitrary root; it performs no closed case-10173 arithmetic.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtDerivativeEval
Ancestors
  compute_registeredCase10173ActualSqrtHessianTrace
  compute_registeredCase10173SourceDerivativeEval
Libs
  bossLib preamble intLib

Theorem bounded_interval64_self_add_strict_positive:
  (case interval of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_add interval interval = SOME twice ==>
  (case twice of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper)
Proof
  Cases_on `interval`
  >> Cases_on `twice`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_actual_sqrt_derivative_eval:
  bounded_case10173_source_positive_q_interval64_exact root root_decimal /\
  (case root_decimal of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_add root_decimal root_decimal = SOME twice /\
  (case twice of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  bounded_interval64_positive_inv_certificate_decimal twice derivative /\
  (case derivative of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  155 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [App «candle_cv_q_dim_jet_sqrt_d» [from_cv root]])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv derivative)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_conversion
  >> mp_tac
       (compute_boundedPositiveQShapeTheory.bounded_object_positive_q_interval64_decimal_shape
        |> Q.INST [`encoded` |-> `root`, `result` |-> `root_decimal`])
  >> impl_tac >- first_assum ACCEPT_TAC
  >> strip_tac
  >> Cases_on `root_decimal`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b`
  >> fs
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
  >> Cases_on `twice`
  >> Cases_on `derivative`
  >> Cases_on `b`
  >> Cases_on `b0`
  >> Cases_on `b'`
  >> Cases_on `b`
  >> Cases_on `b''`
  >> Cases_on `b0'`
  >> Cases_on `b'''`
  >> Cases_on `b`
  >> gvs
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
  >> match_mp_tac
       (SIMP_RULE std_ss
         [arithmeticTheory.SUC_SUB1, compute_execTheory.from_cv_def]
         (Q.INST
           [`source_lower` |-> `lower_value`,
            `source_lower_denominator` |->
              `SUC lower_denominator_minus_one`,
            `source_upper` |-> `upper_value`,
            `source_upper_denominator` |->
              `SUC upper_denominator_minus_one`,
            `sqrt_lower` |-> `c`, `sqrt_upper` |-> `c'`,
            `twice_lower` |-> `c''`, `twice_upper` |-> `c'''`,
            `derivative_lower` |-> `c''''`,
            `derivative_upper` |-> `c'''''`,
            `clock` |-> `clock`, `refs` |-> `refs`]
           compute_registeredCase10173SourceDerivativeEvalTheory.registered_case10173_source_sqrt_derivative_decimal_eval))
  >> fs
       [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_def,
        compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_endpoint64_exact_def,
        compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        arithmeticTheory.SUC_SUB1]
  >> `w2n c <> 0 /\ w2n c' <> 0` by
       metis_tac [wordsTheory.w2n_eq_0]
  >> `0 < w2n c /\ 0 < w2n c'` by intLib.ARITH_TAC
  >> `0 < SUC lower_denominator_minus_one * w2n c /\
      0 < SUC upper_denominator_minus_one * w2n c'` by simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
