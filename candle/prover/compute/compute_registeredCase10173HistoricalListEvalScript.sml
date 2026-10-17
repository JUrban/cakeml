(*****************************************************************************
 * Registered evaluator semantics for historical interval constants and
 * fixed-arity list constructors.
 *
 * These small carriers are shared by the center gradient, Hessian, and the
 * recursive interval sums.  Keeping them above the changing analytic proofs
 * gives those proofs a cheap, reusable list boundary.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalListEval
Ancestors
  compute_registeredCase10173HistoricalIntervalEval
Libs
  bossLib preamble

Definition registered_case10173_fs_one_body_def:
  registered_case10173_fs_one_body =
    Pair (App «candle_cv_fs_scale» []) (Num 0)
End

Definition registered_case10173_fs_interval_one_body_def:
  registered_case10173_fs_interval_one_body =
    Pair (App «candle_cv_fs_one» []) (App «candle_cv_fs_one» [])
End

Definition registered_case10173_cv_list_def:
  registered_case10173_cv_list ([]:cv list) = (Num 0:cv) /\
  registered_case10173_cv_list (value::values) =
    Pair value (registered_case10173_cv_list values)
End

Definition registered_case10173_fs_angle_six_body_def:
  registered_case10173_fs_angle_six_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f») (Num 0))))))
End

Definition registered_case10173_fs_angle_seven_body_def:
  registered_case10173_fs_angle_seven_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f»)
                (Pair (Var «g») (Num 0)))))))
End

Definition registered_case10173_fs_angle_ten_body_def:
  registered_case10173_fs_angle_ten_body =
    Pair (Var «a»)
      (Pair (Var «b»)
        (Pair (Var «c»)
          (Pair (Var «d»)
            (Pair (Var «e»)
              (Pair (Var «f»)
                (Pair (Var «g»)
                  (Pair (Var «h»)
                    (Pair (Var «i»)
                      (Pair (Var «j») (Num 0))))))))))
End

Theorem registered_case10173_fs_one_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_one» =
    SOME ([],registered_case10173_fs_one_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_one_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_one» =
    SOME ([],registered_case10173_fs_interval_one_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_six_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_six» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»],
       registered_case10173_fs_angle_six_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_seven_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_seven» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»;«g»],
       registered_case10173_fs_angle_seven_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_ten_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_ten» =
    SOME
      ([«a»;«b»;«c»;«d»;«e»;«f»;«g»;«h»;«i»;«j»],
       registered_case10173_fs_angle_ten_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_one_eval:
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_one» []) (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Num 1000000000000) (Num 0))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_one_lookup,
        registered_case10173_fs_one_body_def,
        compute_execTheory.from_cv_def,
        compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_zero_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_zero» []) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 0) (Num 0))
          (Pair (Num 0) (Num 0)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_zero_lookup,
        compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_interval_zero_body_def,
        compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_zero_eval,
        compute_execTheory.from_cv_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_one_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_one» []) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Num 1000000000000) (Num 0))
          (Pair (Num 1000000000000) (Num 0)))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_interval_one_lookup,
        registered_case10173_fs_interval_one_body_def,
        compute_execTheory.from_cv_def,
        registered_case10173_fs_one_lookup,
        registered_case10173_fs_one_body_def,
        compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_angle_six_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_six»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [a;b;c;d;e;f])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_angle_six_lookup,
        registered_case10173_fs_angle_six_body_def,
        registered_case10173_cv_list_def,
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

Theorem registered_case10173_fs_angle_seven_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_seven»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f;
         from_cv g]) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [a;b;c;d;e;f;g])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_angle_seven_lookup,
        registered_case10173_fs_angle_seven_body_def,
        registered_case10173_cv_list_def,
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

Theorem registered_case10173_fs_angle_ten_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_ten»
        [from_cv a;from_cv b;from_cv c;from_cv d;from_cv e;from_cv f;
         from_cv g;from_cv h;from_cv i;from_cv j]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_cv_list [a;b;c;d;e;f;g;h;i;j])),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_angle_ten_lookup,
        registered_case10173_fs_angle_ten_body_def,
        registered_case10173_cv_list_def,
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
