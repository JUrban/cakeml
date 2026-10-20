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

Definition registered_case10173_q_interval_mul_body_def:
  registered_case10173_q_interval_mul_body =
    Pair
      (App «candle_cv_q_min4»
        [App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Snd (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Snd (Var «j»)]])
      (App «candle_cv_q_max4»
        [App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Fst (Var «i»);Uop Snd (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Fst (Var «j»)];
         App «candle_cv_q_mul» [Uop Snd (Var «i»);Uop Snd (Var «j»)]])
End

Definition registered_case10173_q_min_value_def:
  registered_case10173_q_min_value (left_value:num) (left_denominator:num)
      (right_value:num) (right_denominator:num) =
    if left_value * right_denominator <=
         right_value * left_denominator
    then left_value else right_value
End


Definition registered_case10173_q_min_denominator_def:
  registered_case10173_q_min_denominator (left_value:num)
      (left_denominator:num) (right_value:num) (right_denominator:num) =
    if left_value * right_denominator <=
         right_value * left_denominator
    then left_denominator else right_denominator
End


Definition registered_case10173_q_max_value_def:
  registered_case10173_q_max_value (left_value:num) (left_denominator:num)
      (right_value:num) (right_denominator:num) =
    if left_value * right_denominator <=
         right_value * left_denominator
    then right_value else left_value
End


Definition registered_case10173_q_max_denominator_def:
  registered_case10173_q_max_denominator (left_value:num)
      (left_denominator:num) (right_value:num) (right_denominator:num) =
    if left_value * right_denominator <=
         right_value * left_denominator
    then right_denominator else left_denominator
End

Definition registered_case10173_q_min4_value_def:
  registered_case10173_q_min4_value
      (a_value:num) (a_denominator:num)
      (b_value:num) (b_denominator:num)
      (c_value:num) (c_denominator:num)
      (d_value:num) (d_denominator:num) =
    registered_case10173_q_min_value
      (registered_case10173_q_min_value
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_min_denominator
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_min_value
        c_value c_denominator d_value d_denominator)
      (registered_case10173_q_min_denominator
        c_value c_denominator d_value d_denominator)
End


Definition registered_case10173_q_min4_denominator_def:
  registered_case10173_q_min4_denominator
      (a_value:num) (a_denominator:num)
      (b_value:num) (b_denominator:num)
      (c_value:num) (c_denominator:num)
      (d_value:num) (d_denominator:num) =
    registered_case10173_q_min_denominator
      (registered_case10173_q_min_value
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_min_denominator
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_min_value
        c_value c_denominator d_value d_denominator)
      (registered_case10173_q_min_denominator
        c_value c_denominator d_value d_denominator)
End


Definition registered_case10173_q_max4_value_def:
  registered_case10173_q_max4_value
      (a_value:num) (a_denominator:num)
      (b_value:num) (b_denominator:num)
      (c_value:num) (c_denominator:num)
      (d_value:num) (d_denominator:num) =
    registered_case10173_q_max_value
      (registered_case10173_q_max_value
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_max_denominator
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_max_value
        c_value c_denominator d_value d_denominator)
      (registered_case10173_q_max_denominator
        c_value c_denominator d_value d_denominator)
End


Definition registered_case10173_q_max4_denominator_def:
  registered_case10173_q_max4_denominator
      (a_value:num) (a_denominator:num)
      (b_value:num) (b_denominator:num)
      (c_value:num) (c_denominator:num)
      (d_value:num) (d_denominator:num) =
    registered_case10173_q_max_denominator
      (registered_case10173_q_max_value
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_max_denominator
        a_value a_denominator b_value b_denominator)
      (registered_case10173_q_max_value
        c_value c_denominator d_value d_denominator)
      (registered_case10173_q_max_denominator
        c_value c_denominator d_value d_denominator)
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

Theorem registered_case10173_q_interval_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_mul» =
    SOME ([«i»;«j»],registered_case10173_q_interval_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_min4_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_min4»
        [from_cv a;from_cv b;from_cv c;from_cv d])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«a»,from_cv a);(«b»,from_cv b);
         («c»,from_cv c);(«d»,from_cv d)]
        registered_case10173_q_min4_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_q_min4_lookup]
QED

Theorem registered_case10173_q_max4_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_max4»
        [from_cv a;from_cv b;from_cv c;from_cv d])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«a»,from_cv a);(«b»,from_cv b);
         («c»,from_cv c);(«d»,from_cv d)]
        registered_case10173_q_max4_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_q_max4_lookup]
QED

Theorem registered_case10173_q_interval_mul_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_mul» [from_cv i;from_cv j])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv i);(«j»,from_cv j)]
        registered_case10173_q_interval_mul_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_q_interval_mul_lookup]
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

Theorem registered_case10173_q_min_positive_denominator_eval:
  0 < (left_denominator:num) /\ 0 < (right_denominator:num) /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_min»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num (left_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num (right_denominator - 1)) : cv)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_min_value
                left_value left_denominator
                right_value right_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_min_denominator
              left_value left_denominator
              right_value right_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_q_min_positive_eval,
        registered_case10173_q_min_value_def,
        registered_case10173_q_min_denominator_def]
  >> Cases_on
       `left_value * right_denominator <=
        left_denominator * right_value`
  >> fs [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_q_max_positive_denominator_eval:
  0 < (left_denominator:num) /\ 0 < (right_denominator:num) /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_max»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num (left_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num (right_denominator - 1)) : cv)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_max_value
                left_value left_denominator
                right_value right_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_max_denominator
              left_value left_denominator
              right_value right_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> simp
       [registered_case10173_q_max_positive_eval,
        registered_case10173_q_max_value_def,
        registered_case10173_q_max_denominator_def]
  >> Cases_on
       `left_value * right_denominator <=
        left_denominator * right_value`
  >> fs [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_q_mul_positive_denominator_eval:
  0 < left_denominator /\ 0 < right_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [from_cv
          (Pair (Pair (Num left_value) (Num 0))
            (Num (left_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num right_value) (Num 0))
            (Num (right_denominator - 1)) : cv)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (left_value * right_value)) (Num 0))
          (Num (left_denominator * right_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173SqrtCertificateEvalTheory.registered_case10173_q_mul_positive_eval]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_mul_positive_denominator_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num left_value) (Num 0))
          (Num (left_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num right_value) (Num 0))
          (Num (right_denominator - 1)) : cv)),refs) /\
  0 < left_denominator /\ 0 < right_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (left_value * right_value)) (Num 0))
          (Num (left_denominator * right_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_mul»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num (left_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num (right_denominator - 1)) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_mul_positive_denominator_eval]
QED

Theorem registered_case10173_q_mul_fst_fst_positive_eval:
  0 < x_lower_denominator /\ 0 < y_lower_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [Uop Fst
          (from_cv
            (Pair
              (Pair (Pair (Num x_lower) (Num 0))
                (Num (x_lower_denominator - 1)))
              x_upper : cv));
         Uop Fst
          (from_cv
            (Pair
              (Pair (Pair (Num y_lower) (Num 0))
                (Num (y_lower_denominator - 1)))
              y_upper : cv))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (x_lower * y_lower)) (Num 0))
          (Num
            (x_lower_denominator * y_lower_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule
       (Q.INST
         [`left_value` |-> `x_lower`,
          `left_denominator` |-> `x_lower_denominator`,
          `right_value` |-> `y_lower`,
          `right_denominator` |-> `y_lower_denominator`]
         registered_case10173_q_mul_positive_denominator_results_eval)
  >> rpt conj_tac
  >> simp
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_mul_fst_snd_positive_eval:
  0 < x_lower_denominator /\ 0 < y_upper_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [Uop Fst
          (from_cv
            (Pair
              (Pair (Pair (Num x_lower) (Num 0))
                (Num (x_lower_denominator - 1)))
              x_upper : cv));
         Uop Snd
          (from_cv
            (Pair y_lower
              (Pair (Pair (Num y_upper) (Num 0))
                (Num (y_upper_denominator - 1))) : cv))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (x_lower * y_upper)) (Num 0))
          (Num
            (x_lower_denominator * y_upper_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule
       (Q.INST
         [`left_value` |-> `x_lower`,
          `left_denominator` |-> `x_lower_denominator`,
          `right_value` |-> `y_upper`,
          `right_denominator` |-> `y_upper_denominator`]
         registered_case10173_q_mul_positive_denominator_results_eval)
  >> rpt conj_tac
  >> simp
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_mul_snd_fst_positive_eval:
  0 < x_upper_denominator /\ 0 < y_lower_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [Uop Snd
          (from_cv
            (Pair x_lower
              (Pair (Pair (Num x_upper) (Num 0))
                (Num (x_upper_denominator - 1))) : cv));
         Uop Fst
          (from_cv
            (Pair
              (Pair (Pair (Num y_lower) (Num 0))
                (Num (y_lower_denominator - 1)))
              y_upper : cv))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (x_upper * y_lower)) (Num 0))
          (Num
            (x_upper_denominator * y_lower_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule
       (Q.INST
         [`left_value` |-> `x_upper`,
          `left_denominator` |-> `x_upper_denominator`,
          `right_value` |-> `y_lower`,
          `right_denominator` |-> `y_lower_denominator`]
         registered_case10173_q_mul_positive_denominator_results_eval)
  >> rpt conj_tac
  >> simp
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_mul_snd_snd_positive_eval:
  0 < x_upper_denominator /\ 0 < y_upper_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_mul»
        [Uop Snd
          (from_cv
            (Pair x_lower
              (Pair (Pair (Num x_upper) (Num 0))
                (Num (x_upper_denominator - 1))) : cv));
         Uop Snd
          (from_cv
            (Pair y_lower
              (Pair (Pair (Num y_upper) (Num 0))
                (Num (y_upper_denominator - 1))) : cv))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (x_upper * y_upper)) (Num 0))
          (Num
            (x_upper_denominator * y_upper_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule
       (Q.INST
         [`left_value` |-> `x_upper`,
          `left_denominator` |-> `x_upper_denominator`,
          `right_value` |-> `y_upper`,
          `right_denominator` |-> `y_upper_denominator`]
         registered_case10173_q_mul_positive_denominator_results_eval)
  >> rpt conj_tac
  >> simp
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_min_positive_denominator_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num left_value) (Num 0))
          (Num (left_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num right_value) (Num 0))
          (Num (right_denominator - 1)) : cv)),refs) /\
  0 < left_denominator /\ 0 < right_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_min»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_min_value
                left_value left_denominator
                right_value right_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_min_denominator
              left_value left_denominator
              right_value right_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_min»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num (left_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num (right_denominator - 1)) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_min_positive_denominator_eval]
QED

Theorem registered_case10173_q_max_positive_denominator_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num left_value) (Num 0))
          (Num (left_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num right_value) (Num 0))
          (Num (right_denominator - 1)) : cv)),refs) /\
  0 < left_denominator /\ 0 < right_denominator /\ 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_max»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_max_value
                left_value left_denominator
                right_value right_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_max_denominator
              left_value left_denominator
              right_value right_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_max»
            [from_cv
              (Pair (Pair (Num left_value) (Num 0))
                (Num (left_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num right_value) (Num 0))
                (Num (right_denominator - 1)) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_max_positive_denominator_eval]
QED

Theorem registered_case10173_q_min_positive_shape:
  0 < left_value /\ 0 < left_denominator /\
  0 < right_value /\ 0 < right_denominator ==>
  0 < registered_case10173_q_min_value
        left_value left_denominator right_value right_denominator /\
  0 < registered_case10173_q_min_denominator
        left_value left_denominator right_value right_denominator
Proof
  rw
       [registered_case10173_q_min_value_def,
        registered_case10173_q_min_denominator_def]
QED

Theorem registered_case10173_q_max_positive_shape:
  0 < left_value /\ 0 < left_denominator /\
  0 < right_value /\ 0 < right_denominator ==>
  0 < registered_case10173_q_max_value
        left_value left_denominator right_value right_denominator /\
  0 < registered_case10173_q_max_denominator
        left_value left_denominator right_value right_denominator
Proof
  rw
       [registered_case10173_q_max_value_def,
        registered_case10173_q_max_denominator_def]
QED

Theorem registered_case10173_q_min4_positive_shape:
  0 < a_value /\ 0 < a_denominator /\
  0 < b_value /\ 0 < b_denominator /\
  0 < c_value /\ 0 < c_denominator /\
  0 < d_value /\ 0 < d_denominator ==>
  0 < registered_case10173_q_min4_value
        a_value a_denominator b_value b_denominator
        c_value c_denominator d_value d_denominator /\
  0 < registered_case10173_q_min4_denominator
        a_value a_denominator b_value b_denominator
        c_value c_denominator d_value d_denominator
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left_value` |-> `a_value`,
          `left_denominator` |-> `a_denominator`,
          `right_value` |-> `b_value`,
          `right_denominator` |-> `b_denominator`]
         registered_case10173_q_min_positive_shape)
  >> mp_tac
       (Q.INST
         [`left_value` |-> `c_value`,
          `left_denominator` |-> `c_denominator`,
          `right_value` |-> `d_value`,
          `right_denominator` |-> `d_denominator`]
         registered_case10173_q_min_positive_shape)
  >> simp [registered_case10173_q_min4_value_def,
           registered_case10173_q_min4_denominator_def]
  >> metis_tac [registered_case10173_q_min_positive_shape]
QED

Theorem registered_case10173_q_max4_positive_shape:
  0 < a_value /\ 0 < a_denominator /\
  0 < b_value /\ 0 < b_denominator /\
  0 < c_value /\ 0 < c_denominator /\
  0 < d_value /\ 0 < d_denominator ==>
  0 < registered_case10173_q_max4_value
        a_value a_denominator b_value b_denominator
        c_value c_denominator d_value d_denominator /\
  0 < registered_case10173_q_max4_denominator
        a_value a_denominator b_value b_denominator
        c_value c_denominator d_value d_denominator
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left_value` |-> `a_value`,
          `left_denominator` |-> `a_denominator`,
          `right_value` |-> `b_value`,
          `right_denominator` |-> `b_denominator`]
         registered_case10173_q_max_positive_shape)
  >> mp_tac
       (Q.INST
         [`left_value` |-> `c_value`,
          `left_denominator` |-> `c_denominator`,
          `right_value` |-> `d_value`,
          `right_denominator` |-> `d_denominator`]
         registered_case10173_q_max_positive_shape)
  >> simp [registered_case10173_q_max4_value_def,
           registered_case10173_q_max4_denominator_def]
  >> metis_tac [registered_case10173_q_max_positive_shape]
QED

Theorem registered_case10173_q_min4_positive_eval:
  0 < a_denominator /\ 0 < b_denominator /\
  0 < c_denominator /\ 0 < d_denominator /\ 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_min4»
        [from_cv
          (Pair (Pair (Num a_value) (Num 0))
            (Num (a_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num b_value) (Num 0))
            (Num (b_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num c_value) (Num 0))
            (Num (c_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num d_value) (Num 0))
            (Num (d_denominator - 1)) : cv)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_min4_value
                a_value a_denominator b_value b_denominator
                c_value c_denominator d_value d_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_min4_denominator
              a_value a_denominator b_value b_denominator
              c_value c_denominator d_value d_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_min4_unfold]
  >> simp
       [registered_case10173_q_min4_body_def,
        compute_evalTheory.subst_def]
  >> simp_tac std_ss
       [registered_case10173_q_min4_value_def,
        registered_case10173_q_min4_denominator_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_value` |->
              `registered_case10173_q_min_value
                a_value a_denominator b_value b_denominator`,
            `left_denominator` |->
              `registered_case10173_q_min_denominator
                a_value a_denominator b_value b_denominator`,
            `right_value` |->
              `registered_case10173_q_min_value
                c_value c_denominator d_value d_denominator`,
            `right_denominator` |->
              `registered_case10173_q_min_denominator
                c_value c_denominator d_value d_denominator`,
            `clock` |-> `clock - 1`,
            `refs` |-> `refs`]
           registered_case10173_q_min_positive_denominator_results_eval))
  >> rpt conj_tac
  >- rw [registered_case10173_q_min_denominator_def]
  >- rw [registered_case10173_q_min_denominator_def]
  >- intLib.ARITH_TAC
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left_value` |-> `a_value`,
             `left_denominator` |-> `a_denominator`,
             `right_value` |-> `b_value`,
             `right_denominator` |-> `b_denominator`,
             `clock` |-> `clock - 1`,
             `refs` |-> `refs`]
            registered_case10173_q_min_positive_denominator_eval))
      >> rpt conj_tac >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_value` |-> `c_value`,
            `left_denominator` |-> `c_denominator`,
            `right_value` |-> `d_value`,
            `right_denominator` |-> `d_denominator`,
            `clock` |-> `clock - 1`,
            `refs` |-> `refs`]
           registered_case10173_q_min_positive_denominator_eval))
  >> rpt conj_tac >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_max4_positive_eval:
  0 < a_denominator /\ 0 < b_denominator /\
  0 < c_denominator /\ 0 < d_denominator /\ 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_max4»
        [from_cv
          (Pair (Pair (Num a_value) (Num 0))
            (Num (a_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num b_value) (Num 0))
            (Num (b_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num c_value) (Num 0))
            (Num (c_denominator - 1)) : cv);
         from_cv
          (Pair (Pair (Num d_value) (Num 0))
            (Num (d_denominator - 1)) : cv)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_max4_value
                a_value a_denominator b_value b_denominator
                c_value c_denominator d_value d_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_max4_denominator
              a_value a_denominator b_value b_denominator
              c_value c_denominator d_value d_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_max4_unfold]
  >> simp
       [registered_case10173_q_max4_body_def,
        compute_evalTheory.subst_def]
  >> simp_tac std_ss
       [registered_case10173_q_max4_value_def,
        registered_case10173_q_max4_denominator_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_value` |->
              `registered_case10173_q_max_value
                a_value a_denominator b_value b_denominator`,
            `left_denominator` |->
              `registered_case10173_q_max_denominator
                a_value a_denominator b_value b_denominator`,
            `right_value` |->
              `registered_case10173_q_max_value
                c_value c_denominator d_value d_denominator`,
            `right_denominator` |->
              `registered_case10173_q_max_denominator
                c_value c_denominator d_value d_denominator`,
            `clock` |-> `clock - 1`,
            `refs` |-> `refs`]
           registered_case10173_q_max_positive_denominator_results_eval))
  >> rpt conj_tac
  >- rw [registered_case10173_q_max_denominator_def]
  >- rw [registered_case10173_q_max_denominator_def]
  >- intLib.ARITH_TAC
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left_value` |-> `a_value`,
             `left_denominator` |-> `a_denominator`,
             `right_value` |-> `b_value`,
             `right_denominator` |-> `b_denominator`,
             `clock` |-> `clock - 1`,
             `refs` |-> `refs`]
            registered_case10173_q_max_positive_denominator_eval))
      >> rpt conj_tac >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_value` |-> `c_value`,
            `left_denominator` |-> `c_denominator`,
            `right_value` |-> `d_value`,
            `right_denominator` |-> `d_denominator`,
            `clock` |-> `clock - 1`,
            `refs` |-> `refs`]
           registered_case10173_q_max_positive_denominator_eval))
  >> rpt conj_tac >> intLib.ARITH_TAC
QED

Theorem registered_case10173_q_min4_positive_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      a_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num a_value) (Num 0))
          (Num (a_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      b_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num b_value) (Num 0))
          (Num (b_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      c_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num c_value) (Num 0))
          (Num (c_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      d_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num d_value) (Num 0))
          (Num (d_denominator - 1)) : cv)),refs) /\
  0 < a_denominator /\ 0 < b_denominator /\
  0 < c_denominator /\ 0 < d_denominator /\ 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_min4»
        [a_expression;b_expression;c_expression;d_expression]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_min4_value
                a_value a_denominator b_value b_denominator
                c_value c_denominator d_value d_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_min4_denominator
              a_value a_denominator b_value b_denominator
              c_value c_denominator d_value d_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_min4»
            [from_cv
              (Pair (Pair (Num a_value) (Num 0))
                (Num (a_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num b_value) (Num 0))
                (Num (b_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num c_value) (Num 0))
                (Num (c_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num d_value) (Num 0))
                (Num (d_denominator - 1)) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_min4_positive_eval]
QED

Theorem registered_case10173_q_max4_positive_results_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      a_expression (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num a_value) (Num 0))
          (Num (a_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      b_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num b_value) (Num 0))
          (Num (b_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      c_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num c_value) (Num 0))
          (Num (c_denominator - 1)) : cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      d_expression refs =
    (M_success
      (from_cv
        (Pair (Pair (Num d_value) (Num 0))
          (Num (d_denominator - 1)) : cv)),refs) /\
  0 < a_denominator /\ 0 < b_denominator /\
  0 < c_denominator /\ 0 < d_denominator /\ 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_max4»
        [a_expression;b_expression;c_expression;d_expression]) refs =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              (registered_case10173_q_max4_value
                a_value a_denominator b_value b_denominator
                c_value c_denominator d_value d_denominator))
            (Num 0))
          (Num
            (registered_case10173_q_max4_denominator
              a_value a_denominator b_value b_denominator
              c_value c_denominator d_value d_denominator - 1)) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_q_max4»
            [from_cv
              (Pair (Pair (Num a_value) (Num 0))
                (Num (a_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num b_value) (Num 0))
                (Num (b_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num c_value) (Num 0))
                (Num (c_denominator - 1)) : cv);
             from_cv
              (Pair (Pair (Num d_value) (Num 0))
                (Num (d_denominator - 1)) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> simp [registered_case10173_q_max4_positive_eval]
QED

Theorem registered_case10173_q_interval_mul_positive_eval:
  0 < x_lower_denominator /\ 0 < x_upper_denominator /\
  0 < y_lower_denominator /\ 0 < y_upper_denominator /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_mul»
        [from_cv
          (Pair
            (Pair (Pair (Num x_lower) (Num 0))
              (Num (x_lower_denominator - 1)))
            (Pair (Pair (Num x_upper) (Num 0))
              (Num (x_upper_denominator - 1))) : cv);
         from_cv
          (Pair
            (Pair (Pair (Num y_lower) (Num 0))
              (Num (y_lower_denominator - 1)))
            (Pair (Pair (Num y_upper) (Num 0))
              (Num (y_upper_denominator - 1))) : cv)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
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
                  (x_upper_denominator * y_upper_denominator) - 1)))
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
                  (x_upper_denominator * y_upper_denominator) - 1))) : cv)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_q_interval_mul_unfold]
  >> simp
       [registered_case10173_q_interval_mul_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |->
              `Pair
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
                      (x_upper_denominator * y_upper_denominator) - 1)) : cv`,
            `right_result` |->
              `Pair
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
                      (x_upper_denominator * y_upper_denominator) - 1)) : cv`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_q_min4_positive_results_eval)
      >> simp [arithmeticTheory.MULT_POS]
      >> rpt conj_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_q_mul_positive_denominator_results_eval)
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_fst_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_q_max4_positive_results_eval)
  >> simp [arithmeticTheory.MULT_POS]
  >> rpt conj_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_q_mul_positive_denominator_results_eval)
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
