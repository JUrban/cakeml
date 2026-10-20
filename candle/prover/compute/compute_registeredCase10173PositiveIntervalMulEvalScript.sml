(*****************************************************************************
 * Positive exact-rational interval multiplication used by Taylor square root.
 *
 * The historical implementation forms four endpoint products and selects
 * their minimum and maximum before normalization.  This file keeps that
 * source structure visible while proving its execution on positive inputs.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalMulEval
Ancestors
  compute_registeredCase10173PositiveIntervalEval
Libs
  bossLib preamble intLib

Definition registered_case10173_q_min_body_def:
  registered_case10173_q_min_body =
    If (App «candle_cv_q_le» [Var «x»;Var «y»])
      (Var «x») (Var «y»)
End

Definition registered_case10173_q_max_body_def:
  registered_case10173_q_max_body =
    If (App «candle_cv_q_le» [Var «x»;Var «y»])
      (Var «y») (Var «x»)
End

Definition registered_case10173_q_min4_body_def:
  registered_case10173_q_min4_body =
    App «candle_cv_q_min»
      [App «candle_cv_q_min» [Var «a»;Var «b»];
       App «candle_cv_q_min» [Var «c»;Var «d»]]
End

Definition registered_case10173_q_max4_body_def:
  registered_case10173_q_max4_body =
    App «candle_cv_q_max»
      [App «candle_cv_q_max» [Var «a»;Var «b»];
       App «candle_cv_q_max» [Var «c»;Var «d»]]
End

Theorem registered_case10173_q_min_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_min» =
    SOME ([«x»;«y»],registered_case10173_q_min_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_max_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_max» =
    SOME ([«x»;«y»],registered_case10173_q_max_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_min4_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_min4» =
    SOME ([«a»;«b»;«c»;«d»],registered_case10173_q_min4_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_max4_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_max4» =
    SOME ([«a»;«b»;«c»;«d»],registered_case10173_q_max4_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_min_positive_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_min»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (if
          left_value * (right_denominator_minus_one + 1) <=
            right_value * (left_denominator_minus_one + 1)
         then Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one)
         else Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_min_lookup,
        registered_case10173_q_min_body_def,
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
  >> Cases_on
       `left_value * (right_denominator_minus_one + 1) <=
        right_value * (left_denominator_minus_one + 1)`
  >> fs [NOT_LESS_EQUAL,compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_q_max_positive_eval:
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_max»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num left_denominator_minus_one));
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num right_denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (if
          left_value * (right_denominator_minus_one + 1) <=
            right_value * (left_denominator_minus_one + 1)
         then Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one)
         else Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_max_lookup,
        registered_case10173_q_max_body_def,
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
  >> Cases_on
       `left_value * (right_denominator_minus_one + 1) <=
        right_value * (left_denominator_minus_one + 1)`
  >> fs [NOT_LESS_EQUAL,compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_q_min_positive_results_eval:
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
      (App «candle_cv_q_min»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv
        (if
          left_value * (right_denominator_minus_one + 1) <=
            right_value * (left_denominator_minus_one + 1)
         then Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one)
         else Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_min»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one));
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_min_positive_eval]
QED

Theorem registered_case10173_q_max_positive_results_eval:
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
      (App «candle_cv_q_max»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv
        (if
          left_value * (right_denominator_minus_one + 1) <=
            right_value * (left_denominator_minus_one + 1)
         then Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one)
         else Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_max»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num left_denominator_minus_one));
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num right_denominator_minus_one))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_max_positive_eval]
QED

val _ = export_theory ();
