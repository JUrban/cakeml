(*****************************************************************************
 * Registered evaluator semantics for the historical root-record boundary.
 *
 * The strengthened packet already proves the four positive square-root
 * certificate facts.  This theory connects those object facts to the exact
 * historical CakeML certificate and list-check functions.
 *****************************************************************************)
Theory compute_registeredCase10173RootRecordEval
Ancestors
  compute_registeredCase10173AnalyticProgramSqrtEval
  compute_boundedObjectCertificateDecimal
Libs
  bossLib preamble

Definition registered_case10173_hist_bool_not_body_def:
  registered_case10173_hist_bool_not_body =
    If (Var «value») (Num 0) (Num 1)
End

Definition registered_case10173_hist_bool_and_body_def:
  registered_case10173_hist_bool_and_body =
    If (Var «left») (Var «right») (Num 0)
End

Definition registered_case10173_hist_num_le_body_def:
  registered_case10173_hist_num_le_body =
    App «candle_cv_fs_hist_bool_not»
      [Binop Less (Var «right») (Var «left»)]
End

Definition registered_case10173_hist_root_certificate_body_def:
  registered_case10173_hist_root_certificate_body =
    (Let «input_lower» (Uop Fst (Uop Fst (Var «input»))) (Let «input_upper» (Uop Fst (Uop Snd (Var «input»))) (Let «root_lower_pair» (Uop Fst (Var «root_value»)) (Let «root_upper_pair» (Uop Snd (Var «root_value»)) (Let «root_lower» (Uop Fst (Var «root_lower_pair»)) (Let «root_upper» (Uop Fst (Var «root_upper_pair»)) (Let «root_shape» (App «candle_cv_fs_hist_bool_and» [Uop Ispair (Var «root_value»);App «candle_cv_fs_hist_bool_and» [Uop Ispair (Var «root_lower_pair»);App «candle_cv_fs_hist_bool_and» [Uop Ispair (Var «root_upper_pair»);App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_bool_not» [Uop Ispair (Var «root_lower»)];App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_bool_not» [Uop Ispair (Var «root_upper»)];App «candle_cv_fs_hist_bool_and» [Binop Eq (Uop Snd (Var «root_lower_pair»)) (Num 0);Binop Eq (Uop Snd (Var «root_upper_pair»)) (Num 0)]]]]]]) (App «candle_cv_fs_hist_bool_and» [Var «root_shape»;App «candle_cv_fs_hist_bool_and» [Binop Less (Num 0) (Var «input_lower»);App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_num_le» [Var «input_lower»;Var «input_upper»];App «candle_cv_fs_hist_bool_and» [Binop Less (Num 0) (Var «root_lower»);App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_num_le» [Var «root_lower»;Var «root_upper»];App «candle_cv_fs_hist_bool_and» [App «candle_cv_fs_hist_num_le» [Binop Mul (Var «root_lower») (Var «root_lower»);Binop Mul (Var «input_lower») (App «candle_cv_fs_scale» [])];App «candle_cv_fs_hist_num_le» [Binop Mul (Var «input_upper») (App «candle_cv_fs_scale» []);Binop Mul (Var «root_upper») (Var «root_upper»)]]]]]]]))))))))
End

Definition registered_case10173_hist_positive_root_certificate_body_def:
  registered_case10173_hist_positive_root_certificate_body =
    App «candle_cv_fs_hist_bool_and»
      [Binop Eq (Uop Snd (Uop Fst (Var «input»))) (Num 0);
       App «candle_cv_fs_hist_bool_and»
         [Binop Eq (Uop Snd (Uop Snd (Var «input»))) (Num 0);
          App «candle_cv_fs_hist_root_certificate»
            [Var «input»;Var «root_value»]]]
End

Theorem registered_case10173_hist_bool_not_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_bool_not» =
    SOME ([«value»],registered_case10173_hist_bool_not_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_bool_and_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_bool_and» =
    SOME ([«left»;«right»],registered_case10173_hist_bool_and_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_num_le_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_num_le» =
    SOME ([«left»;«right»],registered_case10173_hist_num_le_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_root_certificate_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_root_certificate» =
    SOME
      ([«input»;«root_value»],
       registered_case10173_hist_root_certificate_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_positive_root_certificate_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_positive_root_certificate» =
    SOME
      ([«input»;«root_value»],
       registered_case10173_hist_positive_root_certificate_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_scale» =
    SOME ([],Num 1000000000000)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_positive_root_certificate_eval:
  bounded_object_fs_hist_positive_root_certificate
      (Pair (Pair (Num input_lower) (Num 0))
        (Pair (Num input_upper) (Num 0)))
      (Pair (Pair (Num root_lower) (Num 0))
        (Pair (Num root_upper) (Num 0))) = Num 1 /\
  40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_root_certificate»
        [from_cv
          (Pair (Pair (Num input_lower) (Num 0))
            (Pair (Num input_upper) (Num 0)));
         from_cv
          (Pair (Pair (Num root_lower) (Num 0))
            (Pair (Num root_upper) (Num 0)))]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rw
    [compute_boundedObjectCertificateDecimalTheory.bounded_object_fs_hist_positive_root_certificate_def]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_hist_positive_root_certificate_lookup,
        registered_case10173_hist_positive_root_certificate_body_def,
        registered_case10173_hist_root_certificate_lookup,
        registered_case10173_hist_root_certificate_body_def,
        registered_case10173_hist_bool_and_lookup,
        registered_case10173_hist_bool_and_body_def,
        registered_case10173_hist_bool_not_lookup,
        registered_case10173_hist_bool_not_body_def,
        registered_case10173_hist_num_le_lookup,
        registered_case10173_hist_num_le_body_def,
        registered_case10173_fs_scale_lookup,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_arith_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
