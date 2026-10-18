(*****************************************************************************
 * Packet-independent evaluator refinement for registered source radii.
 *
 * This layer connects the literal rational radius preparation in the
 * registered source to the exact word radii authenticated by the fast
 * packet.  The individual arithmetic lemmas are intentionally symbolic;
 * no closed cell fixture or per-cell evaluator replay is used.
 *****************************************************************************)
Theory compute_registeredCase10173RadiusGeneralEval
Ancestors
  compute_registeredCase10173RadiusBinding
  compute_registeredCase10173QConversionEval
Libs
  bossLib preamble intLib

Definition registered_case10173_lc_zadd_body_def:
  registered_case10173_lc_zadd_body =
    Pair
      (Binop Add (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
      (Binop Add (Uop Snd (Var «x»)) (Uop Snd (Var «y»)))
End

Definition registered_case10173_lc_zscale_body_def:
  registered_case10173_lc_zscale_body =
    Pair
      (Binop Mul (Var «k») (Uop Fst (Var «x»)))
      (Binop Mul (Var «k») (Uop Snd (Var «x»)))
End

Definition registered_case10173_q_den_product_pred_body_def:
  registered_case10173_q_den_product_pred_body =
    Binop Add
      (Binop Add (Var «d1») (Var «d2»))
      (Binop Mul (Var «d1») (Var «d2»))
End

Definition registered_case10173_q_zmul_body_def:
  registered_case10173_q_zmul_body =
    Pair
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Snd (Var «y»))))
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Snd (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Fst (Var «y»))))
End

Definition registered_case10173_q_add_body_def:
  registered_case10173_q_add_body =
    Pair
      (App «candle_cv_lc_zadd»
        [App «candle_cv_lc_zscale»
          [App «candle_cv_q_den» [Var «y»];Uop Fst (Var «x»)];
         App «candle_cv_lc_zscale»
          [App «candle_cv_q_den» [Var «x»];Uop Fst (Var «y»)]])
      (App «candle_cv_q_den_product_pred»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_q_mul_body_def:
  registered_case10173_q_mul_body =
    Pair
      (App «candle_cv_q_zmul»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_q_den_product_pred»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Definition registered_case10173_q_neg_body_def:
  registered_case10173_q_neg_body =
    Pair
      (Pair
        (Uop Snd (Uop Fst (Var «x»)))
        (Uop Fst (Uop Fst (Var «x»))))
      (Uop Snd (Var «x»))
End

Definition registered_case10173_q_half_body_def:
  registered_case10173_q_half_body =
    (Pair (Pair (Num 1) (Num 0)) (Num 1) : compute_exp)
End

Definition registered_case10173_q_radius_body_def:
  registered_case10173_q_radius_body =
    App «candle_cv_q_mul»
      [App «candle_cv_q_half» [];
       App «candle_cv_q_add»
        [Uop Snd (Var «i»);
         App «candle_cv_q_neg» [Uop Fst (Var «i»)]]]
End

Definition registered_case10173_q_radius_list_body_def:
  registered_case10173_q_radius_list_body =
    If (Uop Ispair (Var «boxes»))
      (Pair
        (App «candle_cv_q_radius» [Uop Fst (Var «boxes»)])
        (App «candle_cv_q_radius_list» [Uop Snd (Var «boxes»)]))
      (Num 0)
End

Definition registered_case10173_q_fixed_list_round_upper_body_def:
  registered_case10173_q_fixed_list_round_upper_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_q_fixed_round_upper» [Uop Fst (Var «items»)])
        (App «candle_cv_q_fixed_list_round_upper» [Uop Snd (Var «items»)]))
      (Num 0)
End

Theorem registered_case10173_radius_helper_lookups:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_zadd» =
    SOME ([«x»;«y»],registered_case10173_lc_zadd_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_lc_zscale» =
    SOME ([«k»;«x»],registered_case10173_lc_zscale_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_den_product_pred» =
    SOME
      ([«d1»;«d2»],registered_case10173_q_den_product_pred_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_zmul» =
    SOME ([«x»;«y»],registered_case10173_q_zmul_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_add» =
    SOME ([«x»;«y»],registered_case10173_q_add_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_mul» =
    SOME ([«x»;«y»],registered_case10173_q_mul_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_neg» =
    SOME ([«x»],registered_case10173_q_neg_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_half» =
    SOME ([],registered_case10173_q_half_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_radius» =
    SOME ([«i»],registered_case10173_q_radius_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_radius_list» =
    SOME ([«boxes»],registered_case10173_q_radius_list_body) /\
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_fixed_list_round_upper» =
    SOME
      ([«items»],registered_case10173_q_fixed_list_round_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_radius_positive_eval:
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_radius»
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
            (Num (upper_value * (lower_denominator_minus_one + 1)))
            (Num (lower_value * (upper_denominator_minus_one + 1))))
          (Num
            (1 + 2 *
              (lower_denominator_minus_one +
               upper_denominator_minus_one +
               lower_denominator_minus_one *
                 upper_denominator_minus_one))))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_radius_helper_lookups,
        registered_case10173_lc_zadd_body_def,
        registered_case10173_lc_zscale_body_def,
        registered_case10173_q_den_product_pred_body_def,
        registered_case10173_q_zmul_body_def,
        registered_case10173_q_add_body_def,
        registered_case10173_q_mul_body_def,
        registered_case10173_q_neg_body_def,
        registered_case10173_q_half_body_def,
        registered_case10173_q_radius_body_def,
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

Theorem registered_case10173_q_fixed_round_upper_nonnegative_eval:
  negative <= positive /\
  7 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_round_upper»
        [from_cv
          (Pair (Pair (Num positive) (Num negative))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair
            (Num
              ((1000000000000 * (positive - negative)) DIV
                 (denominator_minus_one + 1) +
               if (1000000000000 * (positive - negative)) MOD
                    (denominator_minus_one + 1) = 0
               then 0 else 1))
            (Num 0))
          (Num 999999999999))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_round_upper_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_fixed_make_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_ceil_div_body_def,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_lookup,
        compute_registeredCase10173QConversionEvalTheory.registered_case10173_q_taylor_model_scale_body_def,
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
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        compute_syntaxTheory.SAFEDIV_def,
        compute_syntaxTheory.SAFEMOD_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on
       `(1000000000000 * (positive - negative)) MOD
          (denominator_minus_one + 1) = 0`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
