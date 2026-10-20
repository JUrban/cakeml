(*****************************************************************************
 * Rational-preserving positive normalized interval multiplication.
 *
 * This is the relation-carrying companion to the existing positive-shape
 * evaluator theorem.  It exposes the exact selected endpoint products before
 * normalization, so later source-to-decimal refinements do not depend on the
 * GCD chosen by the unchanged rational implementation.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalMulNormalizedRelationEval
Ancestors
  compute_registeredCase10173PositiveIntervalMulNormalizedEval
  compute_registeredCase10173PositiveIntervalRelationEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_interval_mul_normalized_positive_relation_eval:
  0 < x_lower /\ 0 < x_lower_denominator /\
  0 < x_upper /\ 0 < x_upper_denominator /\
  0 < y_lower /\ 0 < y_lower_denominator /\
  0 < y_upper /\ 0 < y_upper_denominator /\ 142 < clock ==>
  ?normalized_lower normalized_lower_denominator
   normalized_upper normalized_upper_denominator.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_mul_normalized»
          [from_cv
            (Pair
              (Pair (Pair (Num x_lower) (Num 0))
                (Num (x_lower_denominator - 1)))
              (Pair (Pair (Num x_upper) (Num 0))
                (Num (x_upper_denominator - 1))));
           from_cv
            (Pair
              (Pair (Pair (Num y_lower) (Num 0))
                (Num (y_lower_denominator - 1)))
              (Pair (Pair (Num y_upper) (Num 0))
                (Num (y_upper_denominator - 1))))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair
            (Pair (Pair (Num normalized_lower) (Num 0))
              (Num (normalized_lower_denominator - 1)))
            (Pair (Pair (Num normalized_upper) (Num 0))
              (Num (normalized_upper_denominator - 1))))),refs) /\
    0 < normalized_lower /\ 0 < normalized_lower_denominator /\
    0 < normalized_upper /\ 0 < normalized_upper_denominator /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num normalized_lower) (Num 0))
        (Num (normalized_lower_denominator - 1)))
      (Pair
        (Pair
          (Num
            (registered_case10173_q_min4_value
              (x_lower * y_lower)
                (x_lower_denominator * y_lower_denominator)
              (x_lower * y_upper)
                (x_lower_denominator * y_upper_denominator)
              (x_upper * y_lower)
                (x_upper_denominator * y_lower_denominator)
              (x_upper * y_upper)
                (x_upper_denominator * y_upper_denominator)))
          (Num 0))
        (Num
          (registered_case10173_q_min4_denominator
            (x_lower * y_lower)
              (x_lower_denominator * y_lower_denominator)
            (x_lower * y_upper)
              (x_lower_denominator * y_upper_denominator)
            (x_upper * y_lower)
              (x_upper_denominator * y_lower_denominator)
            (x_upper * y_upper)
              (x_upper_denominator * y_upper_denominator) - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num normalized_upper) (Num 0))
        (Num (normalized_upper_denominator - 1)))
      (Pair
        (Pair
          (Num
            (registered_case10173_q_max4_value
              (x_lower * y_lower)
                (x_lower_denominator * y_lower_denominator)
              (x_lower * y_upper)
                (x_lower_denominator * y_upper_denominator)
              (x_upper * y_lower)
                (x_upper_denominator * y_lower_denominator)
              (x_upper * y_upper)
                (x_upper_denominator * y_upper_denominator)))
          (Num 0))
        (Num
          (registered_case10173_q_max4_denominator
            (x_lower * y_lower)
              (x_lower_denominator * y_lower_denominator)
            (x_lower * y_upper)
              (x_lower_denominator * y_upper_denominator)
            (x_upper * y_lower)
              (x_upper_denominator * y_lower_denominator)
            (x_upper * y_upper)
              (x_upper_denominator * y_upper_denominator) - 1)))
Proof
  strip_tac
  >> qabbrev_tac
       `lower_value =
          registered_case10173_q_min4_value
            (x_lower * y_lower)
              (x_lower_denominator * y_lower_denominator)
            (x_lower * y_upper)
              (x_lower_denominator * y_upper_denominator)
            (x_upper * y_lower)
              (x_upper_denominator * y_lower_denominator)
            (x_upper * y_upper)
              (x_upper_denominator * y_upper_denominator)`
  >> qabbrev_tac
       `lower_denominator =
          registered_case10173_q_min4_denominator
            (x_lower * y_lower)
              (x_lower_denominator * y_lower_denominator)
            (x_lower * y_upper)
              (x_lower_denominator * y_upper_denominator)
            (x_upper * y_lower)
              (x_upper_denominator * y_lower_denominator)
            (x_upper * y_upper)
              (x_upper_denominator * y_upper_denominator)`
  >> qabbrev_tac
       `upper_value =
          registered_case10173_q_max4_value
            (x_lower * y_lower)
              (x_lower_denominator * y_lower_denominator)
            (x_lower * y_upper)
              (x_lower_denominator * y_upper_denominator)
            (x_upper * y_lower)
              (x_upper_denominator * y_lower_denominator)
            (x_upper * y_upper)
              (x_upper_denominator * y_upper_denominator)`
  >> qabbrev_tac
       `upper_denominator =
          registered_case10173_q_max4_denominator
            (x_lower * y_lower)
              (x_lower_denominator * y_lower_denominator)
            (x_lower * y_upper)
              (x_lower_denominator * y_upper_denominator)
            (x_upper * y_lower)
              (x_upper_denominator * y_lower_denominator)
            (x_upper * y_upper)
              (x_upper_denominator * y_upper_denominator)`
  >> `0 < lower_value /\ 0 < lower_denominator` by
       (unabbrev_all_tac
        >> irule
             compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min4_positive_shape
        >> simp [arithmeticTheory.MULT_POS])
  >> `0 < upper_value /\ 0 < upper_denominator` by
       (unabbrev_all_tac
        >> irule
             compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max4_positive_shape
        >> simp [arithmeticTheory.MULT_POS])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_mul»
          [from_cv
            (Pair
              (Pair (Pair (Num x_lower) (Num 0))
                (Num (x_lower_denominator - 1)))
              (Pair (Pair (Num x_upper) (Num 0))
                (Num (x_upper_denominator - 1))));
           from_cv
            (Pair
              (Pair (Pair (Num y_lower) (Num 0))
                (Num (y_lower_denominator - 1)))
              (Pair (Pair (Num y_upper) (Num 0))
                (Num (y_upper_denominator - 1))))]) refs =
      (M_success
        (from_cv
          (Pair
            (Pair (Pair (Num lower_value) (Num 0))
              (Num (lower_denominator - 1)))
            (Pair (Pair (Num upper_value) (Num 0))
              (Num (upper_denominator - 1))))),refs)` by
       (unabbrev_all_tac
        >> irule
             compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_interval_mul_positive_eval
        >> intLib.ARITH_TAC)
  >> mp_tac
       (Q.INST
         [`lower_value` |-> `lower_value`,
          `lower_denominator` |-> `lower_denominator`,
          `upper_value` |-> `upper_value`,
          `upper_denominator` |-> `upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173PositiveIntervalRelationEvalTheory.registered_case10173_q_interval_normalize_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_lower`
  >> qexists_tac `normalized_lower_denominator`
  >> qexists_tac `normalized_upper`
  >> qexists_tac `normalized_upper_denominator`
  >> conj_tac
  >- (irule
        compute_registeredCase10173PositiveIntervalMulNormalizedEvalTheory.registered_case10173_q_interval_mul_normalized_from_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac
           `Pair
              (Pair (Pair (Num lower_value) (Num 0))
                (Num (lower_denominator - 1)))
              (Pair (Pair (Num upper_value) (Num 0))
                (Num (upper_denominator - 1))) : cv`
      >> conj_tac
      >- (PURE_ASM_REWRITE_TAC [] >> simp [])
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> unabbrev_all_tac
  >> simp []
QED

val _ = export_theory ();
