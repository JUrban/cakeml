(*****************************************************************************
 * Positive source-domain evaluation for the historical Taylor square root.
 *
 * The theorem below follows the unchanged source control flow.  It composes
 * the authenticated square-root certificate, positive normalized interval
 * addition and multiplication, and both nonzero guards.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtDomainPositiveEval
Ancestors
  compute_registeredCase10173PositiveIntervalMulNormalizedEval
  compute_registeredCase10173SqrtCertificateCompleteEval
  compute_registeredCase10173SqrtPrimitiveEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fsn_sqrt_domain_positive_eval:
  input_lower * (999999999999 + 1) <=
      input_upper * (999999999999 + 1) /\
  certificate_lower * (certificate_upper_denominator_minus_one + 1) <=
      certificate_upper * (certificate_lower_denominator_minus_one + 1) /\
  (certificate_lower * certificate_lower) * (999999999999 + 1) <=
      input_lower *
        (((certificate_lower_denominator_minus_one + 1) *
          (certificate_lower_denominator_minus_one + 1) - 1) + 1) /\
  input_upper *
      (((certificate_upper_denominator_minus_one + 1) *
        (certificate_upper_denominator_minus_one + 1) - 1) + 1) <=
    (certificate_upper * certificate_upper) * (999999999999 + 1) /\
  0 < input_lower /\ 0 < input_upper /\
  0 < certificate_lower /\ 0 < certificate_upper /\
  144 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_sqrt_domain»
        [from_cv
          (Pair
            (Pair (Pair (Num certificate_lower) (Num 0))
              (Num certificate_lower_denominator_minus_one))
            (Pair (Pair (Num certificate_upper) (Num 0))
              (Num certificate_upper_denominator_minus_one)));
         from_cv
          (Pair
            (Pair (Num input_lower) (Num 0))
            (Pair (Num input_upper) (Num 0)))]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> qabbrev_tac
       `certificate =
          Pair
            (Pair (Pair (Num certificate_lower) (Num 0))
              (Num certificate_lower_denominator_minus_one))
            (Pair (Pair (Num certificate_upper) (Num 0))
              (Num certificate_upper_denominator_minus_one)) : cv`
  >> qabbrev_tac
       `input =
          Pair
            (Pair (Pair (Num input_lower) (Num 0))
              (Num 999999999999))
            (Pair (Pair (Num input_upper) (Num 0))
              (Num 999999999999)) : cv`
  >> mp_tac
       (Q.INST
         [`x_lower` |-> `certificate_lower`,
          `x_lower_denominator` |->
             `certificate_lower_denominator_minus_one + 1`,
          `x_upper` |-> `certificate_upper`,
          `x_upper_denominator` |->
             `certificate_upper_denominator_minus_one + 1`,
          `y_lower` |-> `certificate_lower`,
          `y_lower_denominator` |->
             `certificate_lower_denominator_minus_one + 1`,
          `y_upper` |-> `certificate_upper`,
          `y_upper_denominator` |->
             `certificate_upper_denominator_minus_one + 1`,
          `clock` |-> `clock - 2`,
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
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_add_normalized»
          [from_cv certificate;from_cv certificate]) refs =
      (M_success (from_cv certificate_twice),refs)` by
       (qunabbrev_tac `certificate` >> fs [])
  >> mp_tac
       (Q.INST
         [`x_lower` |-> `input_lower`,
          `x_lower_denominator` |-> `1000000000000`,
          `x_upper` |-> `input_upper`,
          `x_upper_denominator` |-> `1000000000000`,
          `y_lower` |-> `input_lower`,
          `y_lower_denominator` |-> `1000000000000`,
          `y_upper` |-> `input_upper`,
          `y_upper_denominator` |-> `1000000000000`,
          `clock` |-> `clock - 2`,
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
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_add_normalized»
          [from_cv input;from_cv input]) refs =
      (M_success (from_cv input_twice),refs)` by
       (qunabbrev_tac `input` >> fs [])
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
          `clock` |-> `clock - 2`,
          `refs` |-> `refs`]
         compute_registeredCase10173PositiveIntervalMulNormalizedEvalTheory.registered_case10173_q_interval_mul_normalized_positive_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> qabbrev_tac
       `positive_product =
          Pair
            (Pair (Pair (Num normalized_lower'') (Num 0))
              (Num (normalized_lower_denominator'' - 1)))
            (Pair (Pair (Num normalized_upper'') (Num 0))
              (Num (normalized_upper_denominator'' - 1))) : cv`
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_mul_normalized»
          [from_cv certificate_twice;from_cv input_twice]) refs =
      (M_success (from_cv positive_product),refs)` by
       (qunabbrev_tac `certificate_twice`
        >> qunabbrev_tac `input_twice`
        >> qunabbrev_tac `positive_product`
        >> fs [])
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_mul_normalized»
          [App «candle_cv_q_interval_add_normalized»
             [from_cv certificate;from_cv certificate];
           App «candle_cv_q_interval_add_normalized»
             [from_cv input;from_cv input]]) refs =
      (M_success (from_cv positive_product),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 2)
                registered_case10173_historical_chunk16_ceqs
                (App «candle_cv_q_interval_mul_normalized»
                  [from_cv certificate_twice;from_cv input_twice]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> asm_rewrite_tac [])
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_not_zero»
          [App «candle_cv_q_interval_add_normalized»
             [from_cv certificate;from_cv certificate]]) refs =
      (M_success (Num 1),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 2)
                registered_case10173_historical_chunk16_ceqs
                (App «candle_cv_q_interval_not_zero»
                  [from_cv certificate_twice]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> qunabbrev_tac `certificate_twice`
        >> irule
             compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_not_zero_positive_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_not_zero»
          [App «candle_cv_q_interval_mul_normalized»
            [App «candle_cv_q_interval_add_normalized»
               [from_cv certificate;from_cv certificate];
             App «candle_cv_q_interval_add_normalized»
               [from_cv input;from_cv input]]]) refs =
      (M_success (Num 1),refs)` by
       (irule EQ_TRANS
        >> qexists_tac
             `compute_eval (clock - 2)
                registered_case10173_historical_chunk16_ceqs
                (App «candle_cv_q_interval_not_zero»
                  [from_cv positive_product]) refs`
        >> conj_tac
        >- (irule
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
            >> asm_rewrite_tac []
            >> intLib.ARITH_TAC)
        >> qunabbrev_tac `positive_product`
        >> irule
             compute_registeredCase10173PositiveIntervalEvalTheory.registered_case10173_q_interval_not_zero_positive_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 2)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_interval_sqrt_certificate»
          [from_cv input;from_cv certificate]) refs =
      (M_success (Num 1),refs)` by
       (qunabbrev_tac `input`
        >> qunabbrev_tac `certificate`
        >> irule
             compute_registeredCase10173SqrtCertificateCompleteEvalTheory.registered_case10173_q_interval_sqrt_certificate_positive_eval
        >> intLib.ARITH_TAC)
  >> rw
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_sqrt_domain_unfold]
  >> simp
       [compute_registeredCase10173ResultSqrtEvalTheory.registered_case10173_fsn_sqrt_domain_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv input`
  >> conj_tac
  >- (qunabbrev_tac `input`
      >> simp [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`lower` |-> `Pair (Num input_lower) (Num 0):cv`,
                `upper` |-> `Pair (Num input_upper) (Num 0):cv`,
                `clock` |-> `clock - 1`,
                `refs` |-> `refs`]
               compute_registeredCase10173SqrtPrimitiveEvalTheory.registered_case10173_fs_interval_to_q_eval))
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> simp
       [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
