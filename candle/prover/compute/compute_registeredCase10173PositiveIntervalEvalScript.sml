(*****************************************************************************
 * Positive exact-rational interval operations used by Taylor square root.
 *
 * The unchanged historical source normalizes interval endpoints after its
 * arithmetic.  This layer proves that the registered CakeML functions retain
 * the positive rational representation required by the source domain tests.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalEval
Ancestors
  compute_registeredCase10173QNormalizeRelationEval
  compute_registeredCase10173SqrtCertificateEval
Libs
  bossLib preamble intLib

Definition registered_case10173_q_interval_add_body_def:
  registered_case10173_q_interval_add_body =
    Pair
      (App «candle_cv_q_add»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_add»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_q_interval_normalize_body_def:
  registered_case10173_q_interval_normalize_body =
    Pair
      (App «candle_cv_q_normalize» [Uop Fst (Var «i»)])
      (App «candle_cv_q_normalize» [Uop Snd (Var «i»)])
End

Definition registered_case10173_q_interval_add_normalized_body_def:
  registered_case10173_q_interval_add_normalized_body =
    App «candle_cv_q_interval_normalize»
      [App «candle_cv_q_interval_add» [Var «x»;Var «y»]]
End

Definition registered_case10173_q_zero_body_def:
  registered_case10173_q_zero_body =
    (Pair (Pair (Num 0) (Num 0)) (Num 0) : compute_exp)
End

Definition registered_case10173_q_interval_not_zero_body_def:
  registered_case10173_q_interval_not_zero_body =
    If
      (App «candle_cv_q_le»
        [Uop Fst (Var «i»);App «candle_cv_q_zero» []])
      (If
        (App «candle_cv_q_le»
          [App «candle_cv_q_zero» [];Uop Snd (Var «i»)])
        (Num 0) (Num 1))
      (Num 1)
End

Theorem registered_case10173_q_interval_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_add» =
    SOME ([«x»;«y»],registered_case10173_q_interval_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_normalize_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_normalize» =
    SOME ([«i»],registered_case10173_q_interval_normalize_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_add_normalized_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_add_normalized» =
    SOME
      ([«x»;«y»],
       registered_case10173_q_interval_add_normalized_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_zero_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_zero» =
    SOME ([],registered_case10173_q_zero_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_not_zero_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_not_zero» =
    SOME ([«i»],registered_case10173_q_interval_not_zero_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_add» [from_cv x;from_cv y])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv x);(«y»,from_cv y)]
        registered_case10173_q_interval_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_interval_add_lookup]
QED

Theorem registered_case10173_q_interval_normalize_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_normalize» [from_cv i])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv i)]
        registered_case10173_q_interval_normalize_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_interval_normalize_lookup]
QED

Theorem registered_case10173_q_interval_add_normalized_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_add_normalized»
        [from_cv x;from_cv y]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv x);(«y»,from_cv y)]
        registered_case10173_q_interval_add_normalized_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_interval_add_normalized_lookup]
QED

Theorem registered_case10173_q_interval_not_zero_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_not_zero» [from_cv i])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv i)]
        registered_case10173_q_interval_not_zero_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_interval_not_zero_lookup]
QED

Theorem registered_case10173_q_interval_add_normalized_from_results:
  1 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_add» [from_cv x;from_cv y])
      (refs:hol_refs) = (M_success (from_cv added),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_normalize» [from_cv added]) refs =
    (M_success (from_cv normalized),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_add_normalized»
        [from_cv x;from_cv y]) refs =
    (M_success (from_cv normalized),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_interval_add_normalized_unfold]
  >> simp
       [registered_case10173_q_interval_add_normalized_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_interval_normalize» [from_cv added]) refs`
  >> conj_tac
      >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> PURE_ASM_REWRITE_TAC []
  >> simp []
QED

Theorem registered_case10173_q_add_positive_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_add»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (left_value * (right_denominator_minus_one + 1) +
               right_value * (left_denominator_minus_one + 1)))
            (Num 0))
          (Num
            ((left_denominator_minus_one + 1) *
             (right_denominator_minus_one + 1) - 1)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_add_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_add_body_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_lc_zadd_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_lc_zadd_body_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_lc_zscale_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_lc_zscale_body_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_den_product_pred_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_den_product_pred_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_interval_add_positive_eval:
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_add»
        [from_cv
          (Pair
            (Pair (Pair (Num x_lower) (Num 0)) (Num x_lower_d))
            (Pair (Pair (Num x_upper) (Num 0)) (Num x_upper_d)));
         from_cv
          (Pair
            (Pair (Pair (Num y_lower) (Num 0)) (Num y_lower_d))
            (Pair (Pair (Num y_upper) (Num 0)) (Num y_upper_d)))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Pair
              (Num (x_lower * (y_lower_d + 1) +
                    y_lower * (x_lower_d + 1)))
              (Num 0))
            (Num ((x_lower_d + 1) * (y_lower_d + 1) - 1)))
          (Pair
            (Pair
              (Num (x_upper * (y_upper_d + 1) +
                    y_upper * (x_upper_d + 1)))
              (Num 0))
            (Num ((x_upper_d + 1) * (y_upper_d + 1) - 1))))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_interval_add_unfold]
  >> simp
       [registered_case10173_q_interval_add_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |->
              `Pair
                (Pair
                  (Num (x_lower * (y_lower_d + 1) +
                        y_lower * (x_lower_d + 1)))
                  (Num 0))
                (Num ((x_lower_d + 1) * (y_lower_d + 1) - 1))`,
            `right_result` |->
              `Pair
                (Pair
                  (Num (x_upper * (y_upper_d + 1) +
                        y_upper * (x_upper_d + 1)))
                  (Num 0))
                (Num ((x_upper_d + 1) * (y_upper_d + 1) - 1))`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_q_add»
                [from_cv
                  (Pair (Pair (Num x_lower) (Num 0)) (Num x_lower_d));
                 from_cv
                  (Pair (Pair (Num y_lower) (Num 0)) (Num y_lower_d))]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
                compute_evalTheory.compute_eval_def,
                compute_evalTheory.do_uop_def,
                compute_evalTheory.do_fst_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def])
      >> `3 < clock - 1` by intLib.ARITH_TAC
      >> simp [registered_case10173_q_add_positive_eval])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_add»
            [from_cv
              (Pair (Pair (Num x_upper) (Num 0)) (Num x_upper_d));
             from_cv
              (Pair (Pair (Num y_upper) (Num 0)) (Num y_upper_d))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> `3 < clock - 1` by intLib.ARITH_TAC
  >> simp [registered_case10173_q_add_positive_eval]
QED

Theorem registered_case10173_q_interval_normalize_positive_eval:
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
    0 < normalized_upper /\ 0 < normalized_upper_denominator
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `lower_value`,
          `denominator` |-> `lower_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173QNormalizeRelationEvalTheory.registered_case10173_q_normalize_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`positive` |-> `upper_value`,
          `denominator` |-> `upper_denominator`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_registeredCase10173QNormalizeRelationEvalTheory.registered_case10173_q_normalize_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_positive`
  >> qexists_tac `normalized_denominator`
  >> qexists_tac `normalized_positive'`
  >> qexists_tac `normalized_denominator'`
  >> conj_tac
  >- (simp [registered_case10173_q_interval_normalize_unfold]
      >> simp
           [registered_case10173_q_interval_normalize_body_def,
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
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_interval_add_normalized_positive_eval:
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
    0 < normalized_upper /\ 0 < normalized_upper_denominator
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
        >> simp [registered_case10173_q_interval_add_positive_eval]
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
         registered_case10173_q_interval_normalize_positive_eval)
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
          registered_case10173_q_interval_add_normalized_from_results)
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (PURE_ASM_REWRITE_TAC [] >> simp [])
      >> PURE_ASM_REWRITE_TAC []
      >> simp [])
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_interval_not_zero_positive_eval:
  0 < lower_value /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_not_zero»
        [from_cv
          (Pair
            (Pair (Pair (Num lower_value) (Num 0))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num upper_value) (Num 0))
              (Num upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_interval_not_zero_lookup,
        registered_case10173_q_interval_not_zero_body_def,
        registered_case10173_q_zero_lookup,
        registered_case10173_q_zero_body_def,
        compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_le_lookup,
        compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_le_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_den_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
