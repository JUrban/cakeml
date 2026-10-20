(*****************************************************************************
 * Representation-preserving square-root second-derivative evaluation.
 *
 * The literal source doubles the supplied root and input intervals,
 * multiplies and normalizes them, takes the reciprocal, and negates it.
 * Besides the evaluator result, this theorem retains the exact rational
 * identity of every normalized intermediate.  A later decimal binding can
 * therefore authenticate the final rounded interval without depending on
 * the implementation's particular GCD choices.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtSecondDerivativeRelationEval
Ancestors
  compute_registeredCase10173SqrtDerivativeEval
  compute_registeredCase10173PositiveIntervalRelationEval
  compute_registeredCase10173PositiveIntervalMulNormalizedRelationEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_dim_jet_sqrt_dd_positive_relation_eval:
  0 < certificate_lower /\ 0 < certificate_lower_denominator /\
  0 < certificate_upper /\ 0 < certificate_upper_denominator /\
  0 < input_lower /\ 0 < input_lower_denominator /\
  0 < input_upper /\ 0 < input_upper_denominator /\
  145 < clock ==>
  ?certificate_twice_lower certificate_twice_lower_denominator
   certificate_twice_upper certificate_twice_upper_denominator
   input_twice_lower input_twice_lower_denominator
   input_twice_upper input_twice_upper_denominator
   product_lower product_lower_denominator
   product_upper product_upper_denominator.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_dim_jet_sqrt_dd»
          [from_cv
            (Pair
              (Pair (Pair (Num certificate_lower) (Num 0))
                (Num (certificate_lower_denominator - 1)))
              (Pair (Pair (Num certificate_upper) (Num 0))
                (Num (certificate_upper_denominator - 1))));
           from_cv
            (Pair
              (Pair (Pair (Num input_lower) (Num 0))
                (Num (input_lower_denominator - 1)))
              (Pair (Pair (Num input_upper) (Num 0))
                (Num (input_upper_denominator - 1))))])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair
            (Pair (Pair (Num 0) (Num product_lower_denominator))
              (Num (product_lower - 1)))
            (Pair (Pair (Num 0) (Num product_upper_denominator))
              (Num (product_upper - 1))))),refs) /\
    0 < certificate_twice_lower /\
    0 < certificate_twice_lower_denominator /\
    0 < certificate_twice_upper /\
    0 < certificate_twice_upper_denominator /\
    0 < input_twice_lower /\ 0 < input_twice_lower_denominator /\
    0 < input_twice_upper /\ 0 < input_twice_upper_denominator /\
    0 < product_lower /\ 0 < product_lower_denominator /\
    0 < product_upper /\ 0 < product_upper_denominator /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num certificate_twice_lower) (Num 0))
        (Num (certificate_twice_lower_denominator - 1)))
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
      (Pair (Pair (Num certificate_twice_upper) (Num 0))
        (Num (certificate_twice_upper_denominator - 1)))
      (Pair
        (Pair
          (Num
            (certificate_upper * certificate_upper_denominator +
             certificate_upper * certificate_upper_denominator))
          (Num 0))
        (Num
          (certificate_upper_denominator *
             certificate_upper_denominator - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num input_twice_lower) (Num 0))
        (Num (input_twice_lower_denominator - 1)))
      (Pair
        (Pair
          (Num
            (input_lower * input_lower_denominator +
             input_lower * input_lower_denominator))
          (Num 0))
        (Num (input_lower_denominator * input_lower_denominator - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num input_twice_upper) (Num 0))
        (Num (input_twice_upper_denominator - 1)))
      (Pair
        (Pair
          (Num
            (input_upper * input_upper_denominator +
             input_upper * input_upper_denominator))
          (Num 0))
        (Num (input_upper_denominator * input_upper_denominator - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num product_lower) (Num 0))
        (Num (product_lower_denominator - 1)))
      (Pair
        (Pair
          (Num
            (registered_case10173_q_min4_value
              (certificate_twice_lower * input_twice_lower)
                (certificate_twice_lower_denominator *
                   input_twice_lower_denominator)
              (certificate_twice_lower * input_twice_upper)
                (certificate_twice_lower_denominator *
                   input_twice_upper_denominator)
              (certificate_twice_upper * input_twice_lower)
                (certificate_twice_upper_denominator *
                   input_twice_lower_denominator)
              (certificate_twice_upper * input_twice_upper)
                (certificate_twice_upper_denominator *
                   input_twice_upper_denominator)))
          (Num 0))
        (Num
          (registered_case10173_q_min4_denominator
            (certificate_twice_lower * input_twice_lower)
              (certificate_twice_lower_denominator *
                 input_twice_lower_denominator)
            (certificate_twice_lower * input_twice_upper)
              (certificate_twice_lower_denominator *
                 input_twice_upper_denominator)
            (certificate_twice_upper * input_twice_lower)
              (certificate_twice_upper_denominator *
                 input_twice_lower_denominator)
            (certificate_twice_upper * input_twice_upper)
              (certificate_twice_upper_denominator *
                 input_twice_upper_denominator) - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num product_upper) (Num 0))
        (Num (product_upper_denominator - 1)))
      (Pair
        (Pair
          (Num
            (registered_case10173_q_max4_value
              (certificate_twice_lower * input_twice_lower)
                (certificate_twice_lower_denominator *
                   input_twice_lower_denominator)
              (certificate_twice_lower * input_twice_upper)
                (certificate_twice_lower_denominator *
                   input_twice_upper_denominator)
              (certificate_twice_upper * input_twice_lower)
                (certificate_twice_upper_denominator *
                   input_twice_lower_denominator)
              (certificate_twice_upper * input_twice_upper)
                (certificate_twice_upper_denominator *
                   input_twice_upper_denominator)))
          (Num 0))
        (Num
          (registered_case10173_q_max4_denominator
            (certificate_twice_lower * input_twice_lower)
              (certificate_twice_lower_denominator *
                 input_twice_lower_denominator)
            (certificate_twice_lower * input_twice_upper)
              (certificate_twice_lower_denominator *
                 input_twice_upper_denominator)
            (certificate_twice_upper * input_twice_lower)
              (certificate_twice_upper_denominator *
                 input_twice_lower_denominator)
            (certificate_twice_upper * input_twice_upper)
              (certificate_twice_upper_denominator *
                 input_twice_upper_denominator) - 1)))
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
  >> qabbrev_tac
       `certificate_twice =
          Pair
            (Pair (Pair (Num normalized_lower) (Num 0))
              (Num (normalized_lower_denominator - 1)))
            (Pair (Pair (Num normalized_upper) (Num 0))
              (Num (normalized_upper_denominator - 1))) : cv`
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_add_normalized»
          [from_cv
            (Pair
              (Pair (Pair (Num certificate_lower) (Num 0))
                (Num (certificate_lower_denominator - 1)))
              (Pair (Pair (Num certificate_upper) (Num 0))
                (Num (certificate_upper_denominator - 1))));
           from_cv
            (Pair
              (Pair (Pair (Num certificate_lower) (Num 0))
                (Num (certificate_lower_denominator - 1)))
              (Pair (Pair (Num certificate_upper) (Num 0))
                (Num (certificate_upper_denominator - 1))))]) refs =
      (M_success (from_cv certificate_twice),refs)` by
       (qunabbrev_tac `certificate_twice` >> fs [])
  >> mp_tac
       (Q.INST
         [`x_lower` |-> `input_lower`,
          `x_lower_denominator` |-> `input_lower_denominator`,
          `x_upper` |-> `input_upper`,
          `x_upper_denominator` |-> `input_upper_denominator`,
          `y_lower` |-> `input_lower`,
          `y_lower_denominator` |-> `input_lower_denominator`,
          `y_upper` |-> `input_upper`,
          `y_upper_denominator` |-> `input_upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173PositiveIntervalRelationEvalTheory.registered_case10173_q_interval_add_normalized_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qabbrev_tac
       `input_twice =
          Pair
            (Pair (Pair (Num normalized_lower') (Num 0))
              (Num (normalized_lower_denominator' - 1)))
            (Pair (Pair (Num normalized_upper') (Num 0))
              (Num (normalized_upper_denominator' - 1))) : cv`
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_add_normalized»
          [from_cv
            (Pair
              (Pair (Pair (Num input_lower) (Num 0))
                (Num (input_lower_denominator - 1)))
              (Pair (Pair (Num input_upper) (Num 0))
                (Num (input_upper_denominator - 1))));
           from_cv
            (Pair
              (Pair (Pair (Num input_lower) (Num 0))
                (Num (input_lower_denominator - 1)))
              (Pair (Pair (Num input_upper) (Num 0))
                (Num (input_upper_denominator - 1))))]) refs =
      (M_success (from_cv input_twice),refs)` by
       (qunabbrev_tac `input_twice` >> fs [])
  >> mp_tac
       (Q.INST
         [`x_lower` |-> `normalized_lower`,
          `x_lower_denominator` |-> `normalized_lower_denominator`,
          `x_upper` |-> `normalized_upper`,
          `x_upper_denominator` |-> `normalized_upper_denominator`,
          `y_lower` |-> `normalized_lower'`,
          `y_lower_denominator` |-> `normalized_lower_denominator'`,
          `y_upper` |-> `normalized_upper'`,
          `y_upper_denominator` |-> `normalized_upper_denominator'`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173PositiveIntervalMulNormalizedRelationEvalTheory.registered_case10173_q_interval_mul_normalized_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_lower`
  >> qexists_tac `normalized_lower_denominator`
  >> qexists_tac `normalized_upper`
  >> qexists_tac `normalized_upper_denominator`
  >> qexists_tac `normalized_lower'`
  >> qexists_tac `normalized_lower_denominator'`
  >> qexists_tac `normalized_upper'`
  >> qexists_tac `normalized_upper_denominator'`
  >> qexists_tac `normalized_lower''`
  >> qexists_tac `normalized_lower_denominator''`
  >> qexists_tac `normalized_upper''`
  >> qexists_tac `normalized_upper_denominator''`
  >> conj_tac
  >- (rw
       [compute_registeredCase10173SqrtDerivativeEvalTheory.registered_case10173_q_dim_jet_sqrt_dd_unfold]
      >> simp
           [compute_registeredCase10173SqrtDerivativeEvalTheory.registered_case10173_q_dim_jet_sqrt_dd_body_def,
            compute_evalTheory.subst_def]
      >> qabbrev_tac
           `product =
              Pair
                (Pair (Pair (Num normalized_lower'') (Num 0))
                  (Num (normalized_lower_denominator'' - 1)))
                (Pair (Pair (Num normalized_upper'') (Num 0))
                  (Num (normalized_upper_denominator'' - 1))) : cv`
      >> `compute_eval (clock - 1)
            registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_q_interval_mul_normalized»
              [App «candle_cv_q_interval_add_normalized»
                 [from_cv
                    (Pair
                      (Pair (Pair (Num certificate_lower) (Num 0))
                        (Num (certificate_lower_denominator - 1)))
                      (Pair (Pair (Num certificate_upper) (Num 0))
                        (Num (certificate_upper_denominator - 1))));
                  from_cv
                    (Pair
                      (Pair (Pair (Num certificate_lower) (Num 0))
                        (Num (certificate_lower_denominator - 1)))
                      (Pair (Pair (Num certificate_upper) (Num 0))
                        (Num (certificate_upper_denominator - 1))))];
               App «candle_cv_q_interval_add_normalized»
                 [from_cv
                    (Pair
                      (Pair (Pair (Num input_lower) (Num 0))
                        (Num (input_lower_denominator - 1)))
                      (Pair (Pair (Num input_upper) (Num 0))
                        (Num (input_upper_denominator - 1))));
                  from_cv
                    (Pair
                      (Pair (Pair (Num input_lower) (Num 0))
                        (Num (input_lower_denominator - 1)))
                      (Pair (Pair (Num input_upper) (Num 0))
                        (Num (input_upper_denominator - 1))))]]) refs =
          (M_success (from_cv product),refs)` by
           (irule EQ_TRANS
            >> qexists_tac
                 `compute_eval (clock - 1)
                    registered_case10173_historical_chunk16_ceqs
                    (App «candle_cv_q_interval_mul_normalized»
                      [from_cv certificate_twice;from_cv input_twice]) refs`
            >> conj_tac
            >- (irule
                  compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
                >> asm_rewrite_tac []
                >> intLib.ARITH_TAC)
            >> qunabbrev_tac `certificate_twice`
            >> qunabbrev_tac `input_twice`
            >> qunabbrev_tac `product`
            >> asm_rewrite_tac [])
      >> qabbrev_tac
           `inverse_cv =
              Pair
                (Pair
                  (Pair (Num normalized_upper_denominator'') (Num 0))
                  (Num (normalized_upper'' - 1)))
                (Pair
                  (Pair (Num normalized_lower_denominator'') (Num 0))
                  (Num (normalized_lower'' - 1))) : cv`
      >> `compute_eval (clock - 1)
            registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_q_interval_inv» [from_cv product]) refs =
          (M_success (from_cv inverse_cv),refs)` by
           (qunabbrev_tac `product`
            >> qunabbrev_tac `inverse_cv`
            >> mp_tac
                 (Q.INST
                   [`lower_value` |-> `normalized_lower''`,
                    `lower_denominator_minus_one` |->
                      `normalized_lower_denominator'' - 1`,
                    `upper_value` |-> `normalized_upper''`,
                    `upper_denominator_minus_one` |->
                      `normalized_upper_denominator'' - 1`,
                    `clock` |-> `clock - 1`,
                    `refs` |-> `refs`]
                   compute_registeredCase10173SqrtPrimitiveEvalTheory.registered_case10173_q_interval_inv_positive_eval)
            >> impl_tac >- intLib.ARITH_TAC
            >> simp [compute_execTheory.from_cv_def])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_interval_neg» [from_cv inverse_cv]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> conj_tac
          >- intLib.ARITH_TAC
          >> irule EQ_TRANS
          >> qexists_tac
               `compute_eval (clock - 1)
                  registered_case10173_historical_chunk16_ceqs
                  (App «candle_cv_q_interval_inv» [from_cv product]) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
              >> fs [compute_execTheory.from_cv_def]
              >> intLib.ARITH_TAC)
          >> asm_rewrite_tac [])
      >> qunabbrev_tac `inverse_cv`
      >> mp_tac
           (Q.INST
             [`lower_value` |-> `normalized_upper_denominator''`,
              `lower_denominator_minus_one` |-> `normalized_upper'' - 1`,
              `upper_value` |-> `normalized_lower_denominator''`,
              `upper_denominator_minus_one` |-> `normalized_lower'' - 1`,
              `clock` |-> `clock - 1`,
              `refs` |-> `refs`]
             compute_registeredCase10173SqrtDerivativeEvalTheory.registered_case10173_q_interval_neg_positive_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> simp [compute_execTheory.from_cv_def])
  >> simp []
QED

val _ = export_theory ();
