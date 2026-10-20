(*****************************************************************************
 * Registered source-to-decimal refinement for the square-root derivative.
 *
 * This is the first evaluator theorem which joins the unchanged rational
 * source computation to the authenticated fixed-decimal reciprocal consumed
 * by the specialized checker.  Normalization choices are hidden behind the
 * exact rational relation; no closed case-10173 arithmetic occurs here.
 *****************************************************************************)
Theory compute_registeredCase10173SourceDerivativeEval
Ancestors
  compute_boundedCase10173SourceDerivativeBinding
  compute_registeredCase10173SqrtDerivativeRelationEval
  compute_registeredCase10173QDecimalEquiv
  compute_registeredCase10173QConversionEval
Libs
  bossLib preamble wordsLib intLib

Theorem registered_case10173_source_sqrt_derivative_decimal_eval:
  0 < source_lower /\ 0 < source_lower_denominator /\
  0 < source_upper /\ 0 < source_upper_denominator /\
  bounded_signed64_strict_positive (BoundedSigned64 F sqrt_lower) /\
  bounded_signed64_strict_positive (BoundedSigned64 F sqrt_upper) /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num source_lower) (Num 0))
      (Num (source_lower_denominator - 1)))
    (bounded_case10173_positive_endpoint64_q_cv
      (BoundedSigned64 F sqrt_lower)) /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num source_upper) (Num 0))
      (Num (source_upper_denominator - 1)))
    (bounded_case10173_positive_endpoint64_q_cv
      (BoundedSigned64 F sqrt_upper)) /\
  bounded_interval64_add
      (BoundedInterval64 (BoundedSigned64 F sqrt_lower)
        (BoundedSigned64 F sqrt_upper))
      (BoundedInterval64 (BoundedSigned64 F sqrt_lower)
        (BoundedSigned64 F sqrt_upper)) =
    SOME
      (BoundedInterval64 (BoundedSigned64 F twice_lower)
        (BoundedSigned64 F twice_upper)) /\
  bounded_interval64_positive_inv_certificate_decimal
      (BoundedInterval64 (BoundedSigned64 F twice_lower)
        (BoundedSigned64 F twice_upper))
      (BoundedInterval64 (BoundedSigned64 F derivative_lower)
        (BoundedSigned64 F derivative_upper)) /\
  155 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [App «candle_cv_q_dim_jet_sqrt_d»
          [from_cv
            (Pair
              (Pair (Pair (Num source_lower) (Num 0))
                (Num (source_lower_denominator - 1)))
              (Pair (Pair (Num source_upper) (Num 0))
                (Num (source_upper_denominator - 1))))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (BoundedInterval64 (BoundedSigned64 F derivative_lower)
            (BoundedSigned64 F derivative_upper)))),refs)
Proof
  strip_tac
  >> drule
       compute_boundedCase10173SourceDerivativeBindingTheory.bounded_case10173_positive_interval64_self_add_magnitudes
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`certificate_lower` |-> `source_lower`,
          `certificate_lower_denominator` |-> `source_lower_denominator`,
          `certificate_upper` |-> `source_upper`,
          `certificate_upper_denominator` |-> `source_upper_denominator`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_registeredCase10173SqrtDerivativeRelationEvalTheory.registered_case10173_q_dim_jet_sqrt_d_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num twice_lower') (Num 0))
          (Num (twice_lower_denominator - 1)))
        (bounded_case10173_positive_endpoint64_q_cv
          (BoundedSigned64 F twice_lower))` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair
                  (Num
                    (source_lower * source_lower_denominator +
                     source_lower * source_lower_denominator))
                  (Num 0))
                (Num
                  (source_lower_denominator * source_lower_denominator - 1))`
        >> conj_tac >- first_assum ACCEPT_TAC
        >> irule
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair
                  (Num
                    (w2n sqrt_lower * 1000000000000 +
                     w2n sqrt_lower * 1000000000000))
                  (Num 0))
                (Num
                  (1000000000000 * 1000000000000 - 1))`
        >> conj_tac
        >- (irule
              compute_boundedQRelationAlgebraTheory.bounded_case10173_positive_q_add_cv_equiv
            >> fs
                 [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def])
        >> irule
             compute_boundedCase10173SourceDerivativeBindingTheory.bounded_case10173_positive_q_self_add_endpoint_equiv
        >> simp [])
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num twice_upper') (Num 0))
          (Num (twice_upper_denominator - 1)))
        (bounded_case10173_positive_endpoint64_q_cv
          (BoundedSigned64 F twice_upper))` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair
                  (Num
                    (source_upper * source_upper_denominator +
                     source_upper * source_upper_denominator))
                  (Num 0))
                (Num
                  (source_upper_denominator * source_upper_denominator - 1))`
        >> conj_tac >- first_assum ACCEPT_TAC
        >> irule
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans
        >> qexists_tac
             `Pair
                (Pair
                  (Num
                    (w2n sqrt_upper * 1000000000000 +
                     w2n sqrt_upper * 1000000000000))
                  (Num 0))
                (Num
                  (1000000000000 * 1000000000000 - 1))`
        >> conj_tac
        >- (irule
              compute_boundedQRelationAlgebraTheory.bounded_case10173_positive_q_add_cv_equiv
            >> fs
                 [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def])
        >> irule
             compute_boundedCase10173SourceDerivativeBindingTheory.bounded_case10173_positive_q_self_add_endpoint_equiv
        >> simp [])
  >> `0 < w2n twice_lower /\ 0 < w2n twice_upper` by
       (fs
          [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_def,
           compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
        >> metis_tac [wordsTheory.w2n_eq_0,
                      arithmeticTheory.NOT_ZERO_LT_ZERO])
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num twice_upper_denominator) (Num 0))
          (Num (twice_upper' - 1)))
        (Pair (Pair (Num 1000000000000) (Num 0))
          (Num (w2n twice_upper - 1)))` by
       (irule
          compute_boundedCase10173SourceDerivativeBindingTheory.bounded_case10173_positive_q_inv_endpoint64_equiv
        >> simp [])
  >> `bounded_case10173_q_cv_equiv
        (Pair (Pair (Num twice_lower_denominator) (Num 0))
          (Num (twice_lower' - 1)))
        (Pair (Pair (Num 1000000000000) (Num 0))
          (Num (w2n twice_lower - 1)))` by
       (irule
          compute_boundedCase10173SourceDerivativeBindingTheory.bounded_case10173_positive_q_inv_endpoint64_equiv
        >> simp [])
  >> `bounded_object_positive_q_interval64_decimal
        (Pair
          (Pair (Pair (Num twice_upper_denominator) (Num 0))
            (Num (twice_upper' - 1)))
          (Pair (Pair (Num twice_lower_denominator) (Num 0))
            (Num (twice_lower' - 1)))) =
      SOME
        (BoundedInterval64 (BoundedSigned64 F derivative_lower)
          (BoundedSigned64 F derivative_upper))` by
       (`bounded_object_positive_q_interval64_decimal
          (Pair
            (Pair (Pair (Num 1000000000000) (Num 0))
              (Num (w2n twice_upper - 1)))
            (Pair (Pair (Num 1000000000000) (Num 0))
              (Num (w2n twice_lower - 1)))) =
        SOME
          (BoundedInterval64 (BoundedSigned64 F derivative_lower)
            (BoundedSigned64 F derivative_upper))` by
          metis_tac
            [compute_boundedCase10173SourceDerivativeBindingTheory.bounded_case10173_positive_inv_certificate_q_conversion]
        >> mp_tac
             (Q.INST
               [`left_lower` |-> `twice_upper_denominator`,
                `left_lower_denominator` |-> `twice_upper'`,
                `right_lower` |-> `1000000000000`,
                `right_lower_denominator` |-> `w2n (twice_upper:word64)`,
                `left_upper` |-> `twice_lower_denominator`,
                `left_upper_denominator` |-> `twice_lower'`,
                `right_upper` |-> `1000000000000`,
                `right_upper_denominator` |-> `w2n (twice_lower:word64)`]
               compute_registeredCase10173QDecimalEquivTheory.registered_case10173_positive_q_interval64_decimal_equiv)
        >> impl_tac >- simp []
        >> strip_tac
        >> metis_tac [])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_of_q»
            [from_cv
              (Pair
                (Pair (Pair (Num twice_upper_denominator) (Num 0))
                  (Num (twice_upper' - 1)))
                (Pair (Pair (Num twice_lower_denominator) (Num 0))
                  (Num (twice_lower' - 1))))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp [])
  >> irule
       compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_of_q_object_eval
  >> simp []
QED

val _ = export_theory ();
