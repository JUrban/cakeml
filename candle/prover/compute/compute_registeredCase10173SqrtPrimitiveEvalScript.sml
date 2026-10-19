(*****************************************************************************
 * Registered primitive semantics used by the historical Taylor square root.
 *
 * This first layer covers the exact fixed-to-rational conversion and the
 * positive rational reciprocal.  The normalization and certificate layers
 * can then be proved without reopening these source-language details.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtPrimitiveEval
Ancestors
  compute_registeredCase10173ResultSqrtAccessorEval
  compute_registeredCase10173RootRecordEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_to_q_body_def:
  registered_case10173_fs_to_q_body =
    Pair (Var «x»)
      (Binop Sub (App «candle_cv_fs_scale» []) (Num 1))
End

Definition registered_case10173_fs_interval_to_q_body_def:
  registered_case10173_fs_interval_to_q_body =
    Pair
      (App «candle_cv_fs_to_q» [Uop Fst (Var «i»)])
      (App «candle_cv_fs_to_q» [Uop Snd (Var «i»)])
End

Definition registered_case10173_q_inv_body_def:
  registered_case10173_q_inv_body =
    If
      (Binop Less
        (Uop Fst (Uop Fst (Var «q»)))
        (Uop Snd (Uop Fst (Var «q»))))
      (Pair
        (Pair (Num 0) (App «candle_cv_q_den» [Var «q»]))
        (Binop Sub
          (Binop Sub
            (Uop Snd (Uop Fst (Var «q»)))
            (Uop Fst (Uop Fst (Var «q»))))
          (Num 1)))
      (If
        (Binop Less
          (Uop Snd (Uop Fst (Var «q»)))
          (Uop Fst (Uop Fst (Var «q»))))
        (Pair
          (Pair (App «candle_cv_q_den» [Var «q»]) (Num 0))
          (Binop Sub
            (Binop Sub
              (Uop Fst (Uop Fst (Var «q»)))
              (Uop Snd (Uop Fst (Var «q»))))
            (Num 1)))
        (Pair (Pair (Num 0) (Num 0)) (Num 0)))
End

Definition registered_case10173_q_interval_inv_body_def:
  registered_case10173_q_interval_inv_body =
    Pair
      (App «candle_cv_q_inv» [Uop Snd (Var «i»)])
      (App «candle_cv_q_inv» [Uop Fst (Var «i»)])
End

Theorem registered_case10173_fs_to_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_to_q» =
    SOME ([«x»],registered_case10173_fs_to_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_to_q_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_to_q» =
    SOME ([«i»],registered_case10173_fs_interval_to_q_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_inv_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_inv» =
    SOME ([«q»],registered_case10173_q_inv_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_q_interval_inv_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_q_interval_inv» =
    SOME ([«i»],registered_case10173_q_interval_inv_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_to_q_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_to_q» [from_cv endpoint]) (refs:hol_refs) =
    (M_success
      (from_cv (Pair endpoint (Num 999999999999))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_to_q_lookup,
        registered_case10173_fs_to_q_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_fs_scale_lookup,
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

Theorem registered_case10173_fs_interval_to_q_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_to_q»
        [from_cv (Pair lower upper)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair lower (Num 999999999999))
          (Pair upper (Num 999999999999)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_interval_to_q_lookup,
        registered_case10173_fs_interval_to_q_body_def,
        registered_case10173_fs_to_q_lookup,
        registered_case10173_fs_to_q_body_def,
        compute_registeredCase10173RootRecordEvalTheory.registered_case10173_fs_scale_lookup,
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
QED

Theorem registered_case10173_q_inv_positive_eval:
  0 < value /\ 1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_inv»
        [from_cv
          (Pair (Pair (Num value) (Num 0))
            (Num denominator_minus_one))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num (denominator_minus_one + 1)) (Num 0))
          (Num (value - 1)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_inv_lookup,
        registered_case10173_q_inv_body_def,
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

Theorem registered_case10173_q_interval_inv_positive_eval:
  0 < lower_value /\ 0 < upper_value /\ 2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_interval_inv»
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
            (Pair (Num (upper_denominator_minus_one + 1)) (Num 0))
            (Num (upper_value - 1)))
          (Pair
            (Pair (Num (lower_denominator_minus_one + 1)) (Num 0))
            (Num (lower_value - 1))))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_q_interval_inv_lookup,
        registered_case10173_q_interval_inv_body_def,
        registered_case10173_q_inv_lookup,
        registered_case10173_q_inv_body_def,
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
