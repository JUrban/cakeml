(*****************************************************************************
 * Registered source evaluation for the rational square-root derivatives.
 *
 * The historical fixed Taylor lift computes
 *
 *   d  = 1 / (s + s)
 *   dd = -1 / ((s + s) * (f + f))
 *
 * before converting the rational intervals back to the fixed carrier.  The
 * theorems below follow that unchanged source for arbitrary positive input
 * intervals.  They deliberately expose existential normalized endpoints:
 * later object refinement depends on the represented rationals, not on a
 * particular GCD chosen by the source normalizer.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtDerivativeEval
Ancestors
  compute_registeredCase10173SqrtDomainPositiveEval
Libs
  bossLib preamble intLib

Definition registered_case10173_q_interval_neg_body_def:
  registered_case10173_q_interval_neg_body =
    Pair
      (App «candle_cv_q_neg» [Uop Snd (Var «x»)])
      (App «candle_cv_q_neg» [Uop Fst (Var «x»)])
End

Definition registered_case10173_q_dim_jet_sqrt_d_body_def:
  registered_case10173_q_dim_jet_sqrt_d_body =
    App «candle_cv_q_interval_inv»
      [App «candle_cv_q_interval_add_normalized»
        [Var «s»;Var «s»]]
End

Definition registered_case10173_q_dim_jet_sqrt_dd_body_def:
  registered_case10173_q_dim_jet_sqrt_dd_body =
    App «candle_cv_q_interval_neg»
      [App «candle_cv_q_interval_inv»
        [App «candle_cv_q_interval_mul_normalized»
          [App «candle_cv_q_interval_add_normalized»
             [Var «s»;Var «s»];
           App «candle_cv_q_interval_add_normalized»
             [Var «f»;Var «f»]]]]
End

Theorem registered_case10173_q_interval_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_neg» =
    SOME ([«x»],registered_case10173_q_interval_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_dim_jet_sqrt_d_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_jet_sqrt_d» =
    SOME ([«s»],registered_case10173_q_dim_jet_sqrt_d_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_dim_jet_sqrt_dd_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_dim_jet_sqrt_dd» =
    SOME ([«s»;«f»],registered_case10173_q_dim_jet_sqrt_dd_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_neg_positive_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_neg»
        [from_cv
          (Pair
            (Pair (Pair (Num lower_value) (Num 0))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num upper_value) (Num 0))
              (Num upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Pair (Num 0) (Num upper_value))
            (Num upper_denominator_minus_one))
          (Pair (Pair (Num 0) (Num lower_value))
            (Num lower_denominator_minus_one)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_interval_neg_lookup,
        registered_case10173_q_interval_neg_body_def,
        compute_registeredCase10173RadiusGeneralEvalTheory.registered_case10173_radius_helper_lookups,
        compute_registeredCase10173RadiusGeneralEvalTheory.registered_case10173_q_neg_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_dim_jet_sqrt_d_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_jet_sqrt_d» [from_cv certificate])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«s»,from_cv certificate)]
        registered_case10173_q_dim_jet_sqrt_d_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_q_dim_jet_sqrt_d_lookup]
QED

Theorem registered_case10173_q_dim_jet_sqrt_dd_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_jet_sqrt_dd»
        [from_cv certificate;from_cv input]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«s»,from_cv certificate);(«f»,from_cv input)]
        registered_case10173_q_dim_jet_sqrt_dd_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_dim_jet_sqrt_dd_lookup]
QED

Theorem registered_case10173_q_dim_jet_sqrt_d_positive_eval:
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
    0 < twice_upper /\ 0 < twice_upper_denominator
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
         compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_add_normalized_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_lower`
  >> qexists_tac `normalized_lower_denominator`
  >> qexists_tac `normalized_upper`
  >> qexists_tac `normalized_upper_denominator`
  >> conj_tac
  >- (rw [registered_case10173_q_dim_jet_sqrt_d_unfold]
      >> simp
           [registered_case10173_q_dim_jet_sqrt_d_body_def,
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
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_dim_jet_sqrt_dd_positive_eval:
  0 < certificate_lower /\ 0 < certificate_lower_denominator /\
  0 < certificate_upper /\ 0 < certificate_upper_denominator /\
  0 < input_lower /\ 0 < input_lower_denominator /\
  0 < input_upper /\ 0 < input_upper_denominator /\
  145 < clock ==>
  ?product_lower product_lower_denominator
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
    0 < product_lower /\ 0 < product_lower_denominator /\
    0 < product_upper /\ 0 < product_upper_denominator
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
         compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_add_normalized_positive_eval)
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
         compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_add_normalized_positive_eval)
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
         compute_registeredCase10173PositiveIntervalMulNormalizedEvalTheory.registered_case10173_q_interval_mul_normalized_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qexists_tac `normalized_lower''`
  >> qexists_tac `normalized_lower_denominator''`
  >> qexists_tac `normalized_upper''`
  >> qexists_tac `normalized_upper_denominator''`
  >> conj_tac
  >- (rw [registered_case10173_q_dim_jet_sqrt_dd_unfold]
      >> simp
           [registered_case10173_q_dim_jet_sqrt_dd_body_def,
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
             registered_case10173_q_interval_neg_positive_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> simp [compute_execTheory.from_cv_def])
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
