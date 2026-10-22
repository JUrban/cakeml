(*****************************************************************************
 * Registered evaluator semantics for historical tuple and point helpers.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalTupleEval
Ancestors
  compute_registeredCase10173HistoricalCombinatorEval
Libs
  bossLib preamble

Definition registered_case10173_fs_hist_four_body_def:
  registered_case10173_fs_hist_four_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d») (Num 0))))
End

Definition registered_case10173_fs_hist_three_body_def:
  registered_case10173_fs_hist_three_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c») (Num 0)))
End

Definition registered_case10173_fs_hist_point_body_def:
  registered_case10173_fs_hist_point_body =
    Pair (Var «value») (Var «value»)
End

Theorem registered_case10173_fs_hist_four_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_four» =
    SOME
      ([«a»;«b»;«c»;«d»],registered_case10173_fs_hist_four_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_three_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_three» =
    SOME ([«a»;«b»;«c»],registered_case10173_fs_hist_three_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_point_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_point» =
    SOME ([«value»],registered_case10173_fs_hist_point_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_four_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_four»
        [from_cv a;from_cv b;from_cv c;from_cv d]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [a;b;c;d])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_four_lookup,
        registered_case10173_fs_hist_four_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_three_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_three»
        [from_cv a;from_cv b;from_cv c]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [a;b;c])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_three_lookup,
        registered_case10173_fs_hist_three_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_point_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_point»
        [from_cv (bounded_signed64_object_cv endpoint)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (BoundedInterval64 endpoint endpoint))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_point_lookup,
        registered_case10173_fs_hist_point_body_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
