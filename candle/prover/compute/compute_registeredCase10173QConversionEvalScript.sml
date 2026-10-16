(*****************************************************************************
 * Registered evaluator semantics for exact positive rational conversion.
 *
 * The authenticated packet decoder uses the same 10^12 floor/ceiling rules
 * as the historical CakeML source.  These lemmas connect the literal source
 * functions to that exact decimal carrier; they are shared by root inputs,
 * production guards, and the final certified calculation.
 *****************************************************************************)
Theory compute_registeredCase10173QConversionEval
Ancestors
  compute_registeredCase10173RootInputsEval
  compute_boundedObjectDecimalQ
Libs
  bossLib preamble

Definition registered_case10173_q_den_body_def:
  registered_case10173_q_den_body =
    Binop Add (Uop Snd (Var «q»)) (Num 1)
End

Definition registered_case10173_q_taylor_model_scale_body_def:
  registered_case10173_q_taylor_model_scale_body =
    (Num 1000000000000 : compute_exp)
End

Definition registered_case10173_q_ceil_div_body_def:
  registered_case10173_q_ceil_div_body =
    Binop Add
      (Binop Div (Var «numerator») (Var «denominator»))
      (If
        (Binop Eq
          (Binop Mod (Var «numerator») (Var «denominator»))
          (Num 0))
        (Num 0) (Num 1))
End

Definition registered_case10173_q_fixed_make_body_def:
  registered_case10173_q_fixed_make_body =
    Pair (Pair (Var «positive») (Var «negative»))
      (Binop Sub (App «candle_cv_q_taylor_model_scale» []) (Num 1))
End

Definition registered_case10173_q_fixed_round_lower_body_def:
  registered_case10173_q_fixed_round_lower_body =
    If
      (Binop Less
        (Uop Fst (Uop Fst (Var «q»)))
        (Uop Snd (Uop Fst (Var «q»))))
      (App «candle_cv_q_fixed_make»
        [Num 0;
         App «candle_cv_q_ceil_div»
           [Binop Mul
             (Binop Sub
               (Uop Snd (Uop Fst (Var «q»)))
               (Uop Fst (Uop Fst (Var «q»))))
             (App «candle_cv_q_taylor_model_scale» []);
            App «candle_cv_q_den» [Var «q»]]])
      (App «candle_cv_q_fixed_make»
        [Binop Div
           (Binop Mul
             (Binop Sub
               (Uop Fst (Uop Fst (Var «q»)))
               (Uop Snd (Uop Fst (Var «q»))))
             (App «candle_cv_q_taylor_model_scale» []))
           (App «candle_cv_q_den» [Var «q»]);
         Num 0])
End

Definition registered_case10173_q_fixed_round_upper_body_def:
  registered_case10173_q_fixed_round_upper_body =
    If
      (Binop Less
        (Uop Fst (Uop Fst (Var «q»)))
        (Uop Snd (Uop Fst (Var «q»))))
      (App «candle_cv_q_fixed_make»
        [Num 0;
         Binop Div
           (Binop Mul
             (Binop Sub
               (Uop Snd (Uop Fst (Var «q»)))
               (Uop Fst (Uop Fst (Var «q»))))
             (App «candle_cv_q_taylor_model_scale» []))
           (App «candle_cv_q_den» [Var «q»])])
      (App «candle_cv_q_fixed_make»
        [App «candle_cv_q_ceil_div»
           [Binop Mul
             (Binop Sub
               (Uop Fst (Uop Fst (Var «q»)))
               (Uop Snd (Uop Fst (Var «q»))))
             (App «candle_cv_q_taylor_model_scale» []);
            App «candle_cv_q_den» [Var «q»]];
         Num 0])
End

Definition registered_case10173_fs_of_q_lower_body_def:
  registered_case10173_fs_of_q_lower_body =
    Uop Fst (App «candle_cv_q_fixed_round_lower» [Var «q»])
End

Definition registered_case10173_fs_of_q_upper_body_def:
  registered_case10173_fs_of_q_upper_body =
    Uop Fst (App «candle_cv_q_fixed_round_upper» [Var «q»])
End

Definition registered_case10173_fs_interval_of_q_body_def:
  registered_case10173_fs_interval_of_q_body =
    Pair
      (App «candle_cv_fs_of_q_lower» [Uop Fst (Var «i»)])
      (App «candle_cv_fs_of_q_upper» [Uop Snd (Var «i»)])
End

Definition registered_case10173_fs_interval_list_of_q_body_def:
  registered_case10173_fs_interval_list_of_q_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_fs_interval_of_q» [Uop Fst (Var «items»)])
        (App «candle_cv_fs_interval_list_of_q» [Uop Snd (Var «items»)]))
      (Num 0)
End

Theorem registered_case10173_q_den_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_den» =
    SOME ([«q»],registered_case10173_q_den_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_taylor_model_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_taylor_model_scale» =
    SOME ([],registered_case10173_q_taylor_model_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_ceil_div_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_ceil_div» =
    SOME
      ([«numerator»;«denominator»],
       registered_case10173_q_ceil_div_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_fixed_make_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_fixed_make» =
    SOME
      ([«positive»;«negative»],
       registered_case10173_q_fixed_make_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_fixed_round_lower_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_fixed_round_lower» =
    SOME ([«q»],registered_case10173_q_fixed_round_lower_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_fixed_round_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_fixed_round_upper» =
    SOME ([«q»],registered_case10173_q_fixed_round_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_of_q_lower_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_of_q_lower» =
    SOME ([«q»],registered_case10173_fs_of_q_lower_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_of_q_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_of_q_upper» =
    SOME ([«q»],registered_case10173_fs_of_q_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_of_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_of_q» =
    SOME ([«i»],registered_case10173_fs_interval_of_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_list_of_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_list_of_q» =
    SOME
      ([«items»],registered_case10173_fs_interval_list_of_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_den_positive_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_den»
        [from_cv (Pair numerator (Num denominator_minus_one))])
      (refs:hol_refs) =
    (M_success (Num (SUC denominator_minus_one)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_den_lookup,
        registered_case10173_q_den_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_taylor_model_scale_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_taylor_model_scale» []) (refs:hol_refs) =
    (M_success (Num 1000000000000),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_taylor_model_scale_lookup,
        registered_case10173_q_taylor_model_scale_body_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_ceil_div_eval:
  0 < denominator /\ 0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_ceil_div»
        [from_cv (Num numerator);from_cv (Num denominator)])
      (refs:hol_refs) =
    (M_success
      (Num
        (numerator DIV denominator +
         if numerator MOD denominator = 0 then 0 else 1)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_ceil_div_lookup,
        registered_case10173_q_ceil_div_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `numerator MOD denominator = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_fixed_make_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_make»
        [from_cv (Num positive);from_cv (Num negative)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Pair (Num positive) (Num negative))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_fixed_make_lookup,
        registered_case10173_q_fixed_make_body_def,
        registered_case10173_q_taylor_model_scale_lookup,
        registered_case10173_q_taylor_model_scale_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_fixed_round_lower_positive_eval:
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_lower»
        [from_cv
          (Pair (Pair (Num value) (Num 0))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              ((1000000000000 * value) DIV
               (denominator_minus_one + 1)))
            (Num 0))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_fixed_round_lower_lookup,
        registered_case10173_q_fixed_round_lower_body_def,
        registered_case10173_q_fixed_make_lookup,
        registered_case10173_q_fixed_make_body_def,
        registered_case10173_q_taylor_model_scale_lookup,
        registered_case10173_q_taylor_model_scale_body_def,
        registered_case10173_q_den_lookup,
        registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_q_fixed_round_upper_positive_eval:
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_upper»
        [from_cv
          (Pair (Pair (Num value) (Num 0))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              ((1000000000000 * value) DIV
                 (denominator_minus_one + 1) +
               if (1000000000000 * value) MOD
                    (denominator_minus_one + 1) = 0
               then 0 else 1))
            (Num 0))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_fixed_round_upper_lookup,
        registered_case10173_q_fixed_round_upper_body_def,
        registered_case10173_q_fixed_make_lookup,
        registered_case10173_q_fixed_make_body_def,
        registered_case10173_q_ceil_div_lookup,
        registered_case10173_q_ceil_div_body_def,
        registered_case10173_q_taylor_model_scale_lookup,
        registered_case10173_q_taylor_model_scale_body_def,
        registered_case10173_q_den_lookup,
        registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `(1000000000000 * value) MOD (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_lower_positive_eval:
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower»
        [from_cv
          (Pair (Pair (Num value) (Num 0))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (Pair
        (Num
          ((1000000000000 * value) DIV
           (denominator_minus_one + 1)))
        (Num 0)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_of_q_lower_lookup,
        registered_case10173_fs_of_q_lower_body_def,
        registered_case10173_q_fixed_round_lower_lookup,
        registered_case10173_q_fixed_round_lower_body_def,
        registered_case10173_q_fixed_make_lookup,
        registered_case10173_q_fixed_make_body_def,
        registered_case10173_q_taylor_model_scale_lookup,
        registered_case10173_q_taylor_model_scale_body_def,
        registered_case10173_q_den_lookup,
        registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_upper_positive_eval:
  9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper»
        [from_cv
          (Pair (Pair (Num value) (Num 0))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (Pair
        (Num
          ((1000000000000 * value) DIV
             (denominator_minus_one + 1) +
           if (1000000000000 * value) MOD
                (denominator_minus_one + 1) = 0
           then 0 else 1))
        (Num 0)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_of_q_upper_lookup,
        registered_case10173_fs_of_q_upper_body_def,
        registered_case10173_q_fixed_round_upper_lookup,
        registered_case10173_q_fixed_round_upper_body_def,
        registered_case10173_q_fixed_make_lookup,
        registered_case10173_q_fixed_make_body_def,
        registered_case10173_q_ceil_div_lookup,
        registered_case10173_q_ceil_div_body_def,
        registered_case10173_q_taylor_model_scale_lookup,
        registered_case10173_q_taylor_model_scale_body_def,
        registered_case10173_q_den_lookup,
        registered_case10173_q_den_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `(1000000000000 * value) MOD (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_lower_positive_fst_eval:
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower»
        [Uop Fst
          (Pair
            (from_cv
              (Pair (Pair (Num value) (Num 0))
                (Num denominator_minus_one)))
            (from_cv other))]) (refs:hol_refs) =
    (M_success
      (Pair
        (Num
          ((1000000000000 * value) DIV
           (denominator_minus_one + 1)))
        (Num 0)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [Uop Fst
            (Pair
              (from_cv
                (Pair (Pair (Num value) (Num 0))
                  (Num denominator_minus_one)))
              (from_cv other))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [from_cv
            (Pair (Pair (Num value) (Num 0))
              (Num denominator_minus_one))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> simp [registered_case10173_fs_of_q_lower_positive_eval]
QED

Theorem registered_case10173_fs_of_q_upper_positive_snd_eval:
  9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper»
        [Uop Snd
          (Pair
            (from_cv other)
            (from_cv
              (Pair (Pair (Num value) (Num 0))
                (Num denominator_minus_one))))]) (refs:hol_refs) =
    (M_success
      (Pair
        (Num
          ((1000000000000 * value) DIV
             (denominator_minus_one + 1) +
           if (1000000000000 * value) MOD
                (denominator_minus_one + 1) = 0
           then 0 else 1))
        (Num 0)),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [Uop Snd
            (Pair
              (from_cv other)
              (from_cv
                (Pair (Pair (Num value) (Num 0))
                  (Num denominator_minus_one))))]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [from_cv
            (Pair (Pair (Num value) (Num 0))
              (Num denominator_minus_one))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp [registered_case10173_fs_of_q_upper_positive_eval]
QED

Theorem registered_case10173_fs_interval_of_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q» [from_cv interval])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv interval)]
        registered_case10173_fs_interval_of_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_of_q_lookup]
QED

Theorem registered_case10173_fs_interval_of_q_positive_eval:
  10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [from_cv
          (Pair
            (Pair (Pair (Num lower_value) (Num 0))
              (Num lower_denominator_minus_one))
            (Pair (Pair (Num upper_value) (Num 0))
              (Num upper_denominator_minus_one)))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              ((1000000000000 * lower_value) DIV
               (lower_denominator_minus_one + 1)))
            (Num 0))
          (Pair
            (Num
              ((1000000000000 * upper_value) DIV
                 (upper_denominator_minus_one + 1) +
               if (1000000000000 * upper_value) MOD
                    (upper_denominator_minus_one + 1) = 0
               then 0 else 1))
            (Num 0)))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_of_q_unfold]
  >> `7 < clock - 1 /\ 9 < clock - 1` by intLib.ARITH_TAC
  >> simp
       [registered_case10173_fs_interval_of_q_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [Uop Fst
            (Pair
              (Pair (Pair (Num lower_value) (Num 0))
                (Num lower_denominator_minus_one))
              (Pair (Pair (Num upper_value) (Num 0))
                (Num upper_denominator_minus_one)))]) refs =
      (M_success
        (Pair
          (Num
            ((1000000000000 * lower_value) DIV
             (lower_denominator_minus_one + 1)))
          (Num 0)),refs)` by
       (irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`clock` |-> `clock - 1`,
               `value` |-> `lower_value`,
               `denominator_minus_one` |->
                 `lower_denominator_minus_one`,
               `other` |->
                 `Pair (Pair (Num upper_value) (Num 0))
                    (Num upper_denominator_minus_one)`,
               `refs` |-> `refs`]
              registered_case10173_fs_of_q_lower_positive_fst_eval))
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [Uop Snd
            (Pair
              (Pair (Pair (Num lower_value) (Num 0))
                (Num lower_denominator_minus_one))
              (Pair (Pair (Num upper_value) (Num 0))
                (Num upper_denominator_minus_one)))]) refs =
      (M_success
        (Pair
          (Num
            ((1000000000000 * upper_value) DIV
               (upper_denominator_minus_one + 1) +
             if (1000000000000 * upper_value) MOD
                  (upper_denominator_minus_one + 1) = 0
             then 0 else 1))
          (Num 0)),refs)` by
       (irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`clock` |-> `clock - 1`,
               `value` |-> `upper_value`,
               `denominator_minus_one` |->
                 `upper_denominator_minus_one`,
               `other` |->
                 `Pair (Pair (Num lower_value) (Num 0))
                    (Num lower_denominator_minus_one)`,
               `refs` |-> `refs`]
              registered_case10173_fs_of_q_upper_positive_snd_eval))
        >> simp [])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_list_of_q_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items)]
        registered_case10173_fs_interval_list_of_q_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_list_of_q_lookup]
QED

Theorem registered_case10173_fs_interval_list_of_q_nil_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q» [from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (Num 0),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_list_of_q_unfold]
  >> simp
       [registered_case10173_fs_interval_list_of_q_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_list_of_q_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q» [from_cv interval])
      (refs:hol_refs) = (M_success (from_cv converted),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q» [from_cv intervals]) refs =
    (M_success (from_cv converted_intervals),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q»
        [from_cv (Pair interval intervals)]) refs =
    (M_success
      (from_cv (Pair converted converted_intervals)),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_list_of_q_unfold]
  >> simp
       [registered_case10173_fs_interval_list_of_q_body_def,
        compute_evalTheory.subst_def]
  >> simp
       [compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_of_q»
          [Uop Fst (Pair (from_cv interval) (from_cv intervals))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_of_q» [from_cv interval]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q»
          [Uop Snd (Pair (from_cv interval) (from_cv intervals))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q» [from_cv intervals]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_of_q_lower_object_eval:
  bounded_object_positive_q_floor64_decimal encoded = SOME endpoint /\
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_lower» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_signed64_object_cv endpoint)),refs)
Proof
  Cases_on `encoded`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c0'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `n'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c0`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
  >> every_case_tac
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_value
  >> gvs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        arithmeticTheory.ADD1,
        registered_case10173_fs_of_q_lower_positive_eval]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_of_q_lower_positive_eval)
  >> simp []
QED

Theorem registered_case10173_fs_of_q_upper_object_eval:
  bounded_object_positive_q_ceil64_decimal encoded = SOME endpoint /\
  9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_of_q_upper» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_signed64_object_cv endpoint)),refs)
Proof
  Cases_on `encoded`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c0'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `n'`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c0`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
  >> every_case_tac
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_value
  >> gvs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        arithmeticTheory.ADD1,
        compute_boundedSignedTheory.bounded_div_ceil,
        registered_case10173_fs_of_q_upper_positive_eval]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_of_q_upper_positive_eval)
  >> simp []
QED

Theorem registered_case10173_fs_interval_of_q_object_components_eval:
  bounded_object_positive_q_floor64_decimal lower =
      SOME lower_endpoint /\
  bounded_object_positive_q_ceil64_decimal upper =
      SOME upper_endpoint /\
  10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [from_cv (Pair lower upper)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_signed64_object_cv lower_endpoint)
          (bounded_signed64_object_cv upper_endpoint))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_interval_of_q_unfold]
  >> simp
       [registered_case10173_fs_interval_of_q_body_def,
        compute_evalTheory.subst_def]
  >> `7 < clock - 1 /\ 9 < clock - 1` by intLib.ARITH_TAC
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_lower»
          [Uop Fst (Pair (from_cv lower) (from_cv upper))]) refs =
      (M_success
        (from_cv (bounded_signed64_object_cv lower_endpoint)),refs)` by
       (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_of_q_lower»
            [Uop Fst (Pair (from_cv lower) (from_cv upper))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_of_q_lower» [from_cv lower]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> simp [registered_case10173_fs_of_q_lower_object_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_of_q_upper»
          [Uop Snd (Pair (from_cv lower) (from_cv upper))]) refs =
      (M_success
        (from_cv (bounded_signed64_object_cv upper_endpoint)),refs)` by
       (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_of_q_upper»
            [Uop Snd (Pair (from_cv lower) (from_cv upper))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_of_q_upper» [from_cv upper]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> simp [registered_case10173_fs_of_q_upper_object_eval])
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_of_q_object_eval:
  bounded_object_positive_q_interval64_decimal encoded = SOME interval /\
  10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q» [from_cv encoded])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv interval)),refs)
Proof
  Cases_on `encoded`
  >> fs
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def]
  >> strip_tac
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_interval_of_q_object_components_eval)
  >> simp []
QED

Theorem registered_case10173_fs_interval_list_of_q_object_eval:
  !encoded intervals clock refs.
    bounded_object_positive_q_interval64_decimal_list encoded =
        SOME intervals /\
    11 * (LENGTH intervals + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_of_q» [from_cv encoded])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_list intervals)),refs)
Proof
  ho_match_mp_tac
    compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_ind
  >> rw
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def]
  >- (simp
        [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
         compute_execTheory.from_cv_def]
      >> irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_interval_list_of_q_nil_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
         registered_case10173_fs_interval_list_of_q_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule registered_case10173_fs_interval_of_q_object_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> simp [])
  >> qpat_x_assum `!interval'. _` (qspec_then `interval'` mp_tac)
  >> simp []
  >> strip_tac
  >> qpat_x_assum `!clock' refs. _`
       (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> simp []
  >> impl_tac
  >- (fs [] >> intLib.ARITH_TAC)
  >> simp []
QED

val _ = export_theory ();
