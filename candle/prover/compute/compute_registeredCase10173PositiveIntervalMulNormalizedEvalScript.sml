(*****************************************************************************
 * Positive normalized exact-rational interval multiplication.
 *
 * This composes the unchanged historical four-endpoint multiplication with
 * the registered interval normalizer.  The existential result deliberately
 * exposes only the positive representation invariant needed by the source
 * square-root domain test.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalMulNormalizedEval
Ancestors
  compute_registeredCase10173PositiveIntervalMulEval
Libs
  bossLib preamble intLib

Definition registered_case10173_q_interval_mul_normalized_body_def:
  registered_case10173_q_interval_mul_normalized_body =
    App «candle_cv_q_interval_normalize»
      [App «candle_cv_q_interval_mul» [Var «x»;Var «y»]]
End

Theorem registered_case10173_q_interval_mul_normalized_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_mul_normalized» =
    SOME
      ([«x»;«y»],
       registered_case10173_q_interval_mul_normalized_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_mul_normalized_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_mul_normalized»
        [from_cv x;from_cv y]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv x);(«y»,from_cv y)]
        registered_case10173_q_interval_mul_normalized_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_interval_mul_normalized_lookup]
QED

Theorem registered_case10173_q_interval_mul_normalized_from_results:
  1 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_mul» [from_cv x;from_cv y])
      (refs:hol_refs) = (M_success (from_cv multiplied),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_normalize» [from_cv multiplied]) refs =
    (M_success (from_cv normalized),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_mul_normalized»
        [from_cv x;from_cv y]) refs =
    (M_success (from_cv normalized),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_interval_mul_normalized_unfold]
  >> simp
       [registered_case10173_q_interval_mul_normalized_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_interval_normalize» [from_cv multiplied]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> PURE_ASM_REWRITE_TAC []
  >> simp []
QED

Theorem registered_case10173_q_interval_mul_normalized_positive_eval:
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
    0 < normalized_upper /\ 0 < normalized_upper_denominator
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
        >> irule registered_case10173_q_min4_positive_shape
        >> simp [arithmeticTheory.MULT_POS])
  >> `0 < upper_value /\ 0 < upper_denominator` by
       (unabbrev_all_tac
        >> irule registered_case10173_q_max4_positive_shape
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
        >> irule registered_case10173_q_interval_mul_positive_eval
        >> intLib.ARITH_TAC)
  >> mp_tac
       (Q.INST
         [`lower_value` |-> `lower_value`,
          `lower_denominator` |-> `lower_denominator`,
          `upper_value` |-> `upper_value`,
          `upper_denominator` |-> `upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_normalize_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_lower`
  >> qexists_tac `normalized_lower_denominator`
  >> qexists_tac `normalized_upper`
  >> qexists_tac `normalized_upper_denominator`
  >> conj_tac
  >- (irule registered_case10173_q_interval_mul_normalized_from_results
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
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
