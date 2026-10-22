(*****************************************************************************
 * Representation-preserving square-root derivative evaluation.
 *
 * The ordinary source computes rational derivatives after normalizing sums
 * and products.  These refinements retain the exact rational identities of
 * those normalized intermediates, allowing the final fixed conversion to be
 * matched to the canonical fast decimal certificates.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtDerivativeRelationEval
Ancestors
  compute_registeredCase10173SqrtDerivativeEval
  compute_registeredCase10173PositiveIntervalRelationEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_dim_jet_sqrt_d_positive_relation_eval:
  0 < certificate_lower /\ 0 < certificate_lower_denominator /\
  0 < certificate_upper /\ 0 < certificate_upper_denominator /\
  144 < clock ==>
  ?twice_lower twice_lower_denominator
   twice_upper twice_upper_denominator.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_jet_sqrt_d»
          [from_cv
            (Pair
              (Pair (Pair (Num certificate_lower) (Num 0))
                (Num (certificate_lower_denominator - 1)))
              (Pair (Pair (Num certificate_upper) (Num 0))
                (Num (certificate_upper_denominator - 1))))])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair
            (Pair (Pair (Num twice_upper_denominator) (Num 0))
              (Num (twice_upper - 1)))
            (Pair (Pair (Num twice_lower_denominator) (Num 0))
              (Num (twice_lower - 1))))),refs) /\
    0 < twice_lower /\ 0 < twice_lower_denominator /\
    0 < twice_upper /\ 0 < twice_upper_denominator /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num twice_lower) (Num 0))
        (Num (twice_lower_denominator - 1)))
      (Pair
        (Pair
          (Num
            (certificate_lower * certificate_lower_denominator +
             certificate_lower * certificate_lower_denominator))
          (Num 0))
        (Num
          (certificate_lower_denominator *
             certificate_lower_denominator - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num twice_upper) (Num 0))
        (Num (twice_upper_denominator - 1)))
      (Pair
        (Pair
          (Num
            (certificate_upper * certificate_upper_denominator +
             certificate_upper * certificate_upper_denominator))
          (Num 0))
        (Num
          (certificate_upper_denominator *
             certificate_upper_denominator - 1)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`x_lower` |-> `certificate_lower`,
          `x_lower_denominator` |-> `certificate_lower_denominator`,
          `x_upper` |-> `certificate_upper`,
          `x_upper_denominator` |-> `certificate_upper_denominator`,
          `y_lower` |-> `certificate_lower`,
          `y_lower_denominator` |-> `certificate_lower_denominator`,
          `y_upper` |-> `certificate_upper`,
          `y_upper_denominator` |-> `certificate_upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173PositiveIntervalRelationEvalTheory.registered_case10173_q_interval_add_normalized_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_lower`
  >> qexists_tac `normalized_lower_denominator`
  >> qexists_tac `normalized_upper`
  >> qexists_tac `normalized_upper_denominator`
  >> conj_tac
  >- (rw
       [compute_registeredCase10173SqrtDerivativeEvalTheory.registered_case10173_q_dim_jet_sqrt_d_unfold]
      >> simp
           [compute_registeredCase10173SqrtDerivativeEvalTheory.registered_case10173_q_dim_jet_sqrt_d_body_def,
            compute_evalTheory.subst_def]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_interval_inv»
                [from_cv
                  (Pair
                    (Pair (Pair (Num normalized_lower) (Num 0))
                      (Num (normalized_lower_denominator - 1)))
                    (Pair (Pair (Num normalized_upper) (Num 0))
                      (Num (normalized_upper_denominator - 1))))]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> fs [compute_execTheory.from_cv_def])
      >> mp_tac
           (Q.INST
             [`lower_value` |-> `normalized_lower`,
              `lower_denominator_minus_one` |->
                `normalized_lower_denominator - 1`,
              `upper_value` |-> `normalized_upper`,
              `upper_denominator_minus_one` |->
                `normalized_upper_denominator - 1`,
              `clock` |-> `clock - 1`,
              `refs` |-> `refs`]
             compute_registeredCase10173SqrtPrimitiveEvalTheory.registered_case10173_q_interval_inv_positive_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> simp [compute_execTheory.from_cv_def])
  >> simp []
QED

val _ = export_theory ();
