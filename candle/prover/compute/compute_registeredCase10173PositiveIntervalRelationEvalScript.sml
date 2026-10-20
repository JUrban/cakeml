(*****************************************************************************
 * Rational-preserving positive interval normalization.
 *
 * This is the relation-carrying companion to the existing positive-shape
 * evaluator theorem.  It records, endpoint by endpoint, that normalization
 * changes only representation and not the rational consumed by later fixed
 * rounding.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalRelationEval
Ancestors
  compute_registeredCase10173PositiveIntervalEval
  compute_registeredCase10173QNormalizePositiveRelationEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_interval_normalize_positive_relation_eval:
  0 < lower_value /\ 0 < lower_denominator /\
  0 < upper_value /\ 0 < upper_denominator /\ 141 < clock ==>
  ?normalized_lower normalized_lower_denominator
   normalized_upper normalized_upper_denominator.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_normalize»
          [from_cv
            (Pair
              (Pair (Pair (Num lower_value) (Num 0))
                (Num (lower_denominator - 1)))
              (Pair (Pair (Num upper_value) (Num 0))
                (Num (upper_denominator - 1))))]) (refs:hol_refs) =
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
      (Pair (Pair (Num lower_value) (Num 0))
        (Num (lower_denominator - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num normalized_upper) (Num 0))
        (Num (normalized_upper_denominator - 1)))
      (Pair (Pair (Num upper_value) (Num 0))
        (Num (upper_denominator - 1)))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `lower_value`,
          `denominator` |-> `lower_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173QNormalizePositiveRelationEvalTheory.registered_case10173_q_normalize_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `upper_value`,
          `denominator` |-> `upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173QNormalizePositiveRelationEvalTheory.registered_case10173_q_normalize_positive_relation_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_positive`
  >> qexists_tac `normalized_denominator`
  >> qexists_tac `normalized_positive'`
  >> qexists_tac `normalized_denominator'`
  >> conj_tac
  >- (simp
       [compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_normalize_unfold]
      >> simp
           [compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_normalize_body_def,
            compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`left_result` |->
                  `Pair (Pair (Num normalized_positive) (Num 0))
                    (Num (normalized_denominator - 1))`,
                `right_result` |->
                  `Pair (Pair (Num normalized_positive') (Num 0))
                    (Num (normalized_denominator' - 1))`]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
      >> conj_tac
      >- (irule EQ_TRANS
          >> qexists_tac
               `compute_eval (clock - 1)
                  registered_case10173_historical_chunk16_ceqs
                  (App «candle_cv_q_normalize»
                    [from_cv
                      (Pair (Pair (Num lower_value) (Num 0))
                        (Num (lower_denominator - 1)))]) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
              >> conj_tac >- intLib.ARITH_TAC
              >> simp
                   [compute_evalTheory.compute_eval_def,
                    compute_evalTheory.do_uop_def,
                    compute_evalTheory.do_fst_def,
                    ml_monadBaseTheory.st_ex_bind_def,
                    ml_monadBaseTheory.st_ex_return_def])
          >> PURE_ASM_REWRITE_TAC []
          >> simp [])
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_normalize»
                [from_cv
                  (Pair (Pair (Num upper_value) (Num 0))
                    (Num (upper_denominator - 1)))]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> simp
               [compute_evalTheory.compute_eval_def,
                compute_evalTheory.do_uop_def,
                compute_evalTheory.do_snd_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def])
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> simp []
QED

Theorem registered_case10173_q_interval_add_normalized_positive_relation_eval:
  0 < x_lower /\ 0 < x_lower_denominator /\
  0 < x_upper /\ 0 < x_upper_denominator /\
  0 < y_lower /\ 0 < y_lower_denominator /\
  0 < y_upper /\ 0 < y_upper_denominator /\ 142 < clock ==>
  ?normalized_lower normalized_lower_denominator
   normalized_upper normalized_upper_denominator.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_add_normalized»
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
            (x_lower * y_lower_denominator +
             y_lower * x_lower_denominator))
          (Num 0))
        (Num (x_lower_denominator * y_lower_denominator - 1))) /\
    bounded_case10173_q_cv_equiv
      (Pair (Pair (Num normalized_upper) (Num 0))
        (Num (normalized_upper_denominator - 1)))
      (Pair
        (Pair
          (Num
            (x_upper * y_upper_denominator +
             y_upper * x_upper_denominator))
          (Num 0))
        (Num (x_upper_denominator * y_upper_denominator - 1)))
Proof
  strip_tac
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_add»
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
            (Pair
              (Pair
                (Num
                  (x_lower * y_lower_denominator +
                   y_lower * x_lower_denominator))
                (Num 0))
              (Num
                (x_lower_denominator * y_lower_denominator - 1)))
            (Pair
              (Pair
                (Num
                  (x_upper * y_upper_denominator +
                   y_upper * x_upper_denominator))
                (Num 0))
              (Num
                (x_upper_denominator * y_upper_denominator - 1))))),refs)` by
       (`4 < clock - 1` by intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_add_positive_eval]
        >> intLib.ARITH_TAC)
  >> mp_tac
       (Q.INST
         [`lower_value` |->
            `x_lower * y_lower_denominator +
             y_lower * x_lower_denominator`,
          `lower_denominator` |->
            `x_lower_denominator * y_lower_denominator`,
          `upper_value` |->
            `x_upper * y_upper_denominator +
             y_upper * x_upper_denominator`,
          `upper_denominator` |->
            `x_upper_denominator * y_upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         registered_case10173_q_interval_normalize_positive_relation_eval)
  >> impl_tac
  >- (conj_tac
      >- (`0 < x_lower * y_lower_denominator` by
            metis_tac [arithmeticTheory.MULT_POS]
          >> intLib.ARITH_TAC)
      >> conj_tac >- metis_tac [arithmeticTheory.MULT_POS]
      >> conj_tac
      >- (`0 < x_upper * y_upper_denominator` by
            metis_tac [arithmeticTheory.MULT_POS]
          >> intLib.ARITH_TAC)
      >> conj_tac >- metis_tac [arithmeticTheory.MULT_POS]
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> qexists_tac `normalized_lower`
  >> qexists_tac `normalized_lower_denominator`
  >> qexists_tac `normalized_upper`
  >> qexists_tac `normalized_upper_denominator`
  >> conj_tac
  >- (irule
        (Q.INST
          [`x` |->
             `Pair
                (Pair (Pair (Num x_lower) (Num 0))
                  (Num (x_lower_denominator - 1)))
                (Pair (Pair (Num x_upper) (Num 0))
                  (Num (x_upper_denominator - 1)))`,
           `y` |->
             `Pair
                (Pair (Pair (Num y_lower) (Num 0))
                  (Num (y_lower_denominator - 1)))
                (Pair (Pair (Num y_upper) (Num 0))
                  (Num (y_upper_denominator - 1)))`,
           `added` |->
             `Pair
                (Pair
                  (Pair
                    (Num
                      (x_lower * y_lower_denominator +
                       y_lower * x_lower_denominator))
                    (Num 0))
                  (Num
                    (x_lower_denominator * y_lower_denominator - 1)))
                (Pair
                  (Pair
                    (Num
                      (x_upper * y_upper_denominator +
                       y_upper * x_upper_denominator))
                    (Num 0))
                  (Num
                    (x_upper_denominator * y_upper_denominator - 1)))`,
           `normalized` |->
             `Pair
                (Pair (Pair (Num normalized_lower) (Num 0))
                  (Num (normalized_lower_denominator - 1)))
                (Pair (Pair (Num normalized_upper) (Num 0))
                  (Num (normalized_upper_denominator - 1)))`,
           `clock` |-> `clock`,
           `refs` |-> `refs`]
          compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_add_normalized_from_results)
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (PURE_ASM_REWRITE_TAC [] >> simp [])
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> simp []
QED

val _ = export_theory ();
