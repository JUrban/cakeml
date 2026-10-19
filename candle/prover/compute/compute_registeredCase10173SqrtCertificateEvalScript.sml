(*****************************************************************************
 * Registered exact-rational certificate primitives for Taylor square root.
 *
 * Positive-rational comparison and multiplication are isolated here so the
 * literal source square-root certificate can later be discharged from the
 * strengthened decimal packet without generic evaluator replay.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtCertificateEval
Ancestors
  compute_registeredCase10173SqrtPrimitiveEval
  compute_registeredCase10173CenterEnvironmentEval
Libs
  bossLib preamble intLib

Definition registered_case10173_q_le_body_def:
  registered_case10173_q_le_body =
    Binop Less
      (Binop Add
        (Binop Mul
          (Uop Fst (Uop Fst (Var «x»)))
          (App «candle_cv_q_den» [Var «y»]))
        (Binop Mul
          (Uop Snd (Uop Fst (Var «y»)))
          (App «candle_cv_q_den» [Var «x»])))
      (Binop Add
        (Binop Add
          (Binop Mul
            (Uop Fst (Uop Fst (Var «y»)))
            (App «candle_cv_q_den» [Var «x»]))
          (Binop Mul
            (Uop Snd (Uop Fst (Var «x»)))
            (App «candle_cv_q_den» [Var «y»])))
        (Num 1))
End

Definition registered_case10173_q_interval_sqrt_certificate_body_def:
  registered_case10173_q_interval_sqrt_certificate_body =
    If
      (App «candle_cv_q_le»
        [Pair (Pair (Num 0) (Num 0)) (Num 0);
         Uop Fst (Var «input»)])
      (If
        (App «candle_cv_q_le»
          [Uop Fst (Var «input»);Uop Snd (Var «input»)])
        (If
          (App «candle_cv_q_le»
            [Pair (Pair (Num 0) (Num 0)) (Num 0);
             Uop Fst (Var «output»)])
          (If
            (App «candle_cv_q_le»
              [Uop Fst (Var «output»);Uop Snd (Var «output»)])
            (If
              (App «candle_cv_q_le»
                [App «candle_cv_q_mul»
                   [Uop Fst (Var «output»);Uop Fst (Var «output»)];
                 Uop Fst (Var «input»)])
              (If
                (App «candle_cv_q_le»
                  [Uop Snd (Var «input»);
                   App «candle_cv_q_mul»
                     [Uop Snd (Var «output»);
                      Uop Snd (Var «output»)]])
                (Num 1) (Num 0))
              (Num 0))
            (Num 0))
          (Num 0))
        (Num 0))
      (Num 0)
End

Theorem registered_case10173_q_le_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_le» =
    SOME ([«x»;«y»],registered_case10173_q_le_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_sqrt_certificate_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_sqrt_certificate» =
    SOME
      ([«input»;«output»],
       registered_case10173_q_interval_sqrt_certificate_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_sqrt_certificate_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [from_cv input;from_cv output]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«input»,from_cv input);(«output»,from_cv output)]
        registered_case10173_q_interval_sqrt_certificate_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_interval_sqrt_certificate_lookup]
QED

Theorem registered_case10173_q_le_positive_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_le»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (Num
        (if
          left_value * (right_denominator_minus_one + 1) <=
          right_value * (left_denominator_minus_one + 1)
         then 1 else 0)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_le_lookup,
        registered_case10173_q_le_body_def,
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
  >> Cases_on
       `left_value * (right_denominator_minus_one + 1) <=
        right_value * (left_denominator_minus_one + 1)`
  >> fs []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_mul_positive_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (left_value * right_value)) (Num 0))
          (Num
            ((left_denominator_minus_one + 1) *
             (right_denominator_minus_one + 1) - 1)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_mul_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_mul_body_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_zmul_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_zmul_body_def,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_den_product_pred_lookup,
        compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_den_product_pred_body_def,
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

Theorem registered_case10173_q_le_positive_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num left_value) (Num 0))
          (Num left_denominator_minus_one))),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num right_value) (Num 0))
          (Num right_denominator_minus_one))),refs) /\
  left_value * (right_denominator_minus_one + 1) <=
    right_value * (left_denominator_minus_one + 1) /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_le»
        [left_expression;right_expression]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_le»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one));
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_le_positive_eval]
QED

Theorem registered_case10173_q_mul_positive_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num left_value) (Num 0))
          (Num left_denominator_minus_one))),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num right_value) (Num 0))
          (Num right_denominator_minus_one))),refs) /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (left_value * right_value)) (Num 0))
          (Num
            ((left_denominator_minus_one + 1) *
             (right_denominator_minus_one + 1) - 1)))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_mul»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one));
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_mul_positive_eval]
QED

val _ = export_theory ();
