(*****************************************************************************
 * Literal registered-evaluator semantics for the fixed Taylor primitives.
 *
 * These are the non-recursive operations used by dot products, weighted
 * Hessian rows, and final Taylor completion.  The theorems are stated at the
 * bounded-object interface so the recursive refinements can reuse them.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorPrimitiveEval
Ancestors
  compute_registeredCase10173TaylorCompletionEval
Libs
  bossLib preamble

Definition registered_case10173_fs_scale_body_def:
  registered_case10173_fs_scale_body = (Num 1000000000000 : compute_exp)
End

Definition registered_case10173_fs_scale_squared_body_def:
  registered_case10173_fs_scale_squared_body =
    Binop Mul (App «candle_cv_fs_scale» []) (App «candle_cv_fs_scale» [])
End

Definition registered_case10173_fs_two_scale_squared_body_def:
  registered_case10173_fs_two_scale_squared_body =
    Binop Mul (Num 2) (App «candle_cv_fs_scale_squared» [])
End

Definition registered_case10173_fs_raw_add_body_def:
  registered_case10173_fs_raw_add_body =
    Pair
      (Binop Add (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
      (Binop Add (Uop Snd (Var «x»)) (Uop Snd (Var «y»)))
End

Definition registered_case10173_fs_raw_neg_body_def:
  registered_case10173_fs_raw_neg_body =
    Pair (Uop Snd (Var «x»)) (Uop Fst (Var «x»))
End

Definition registered_case10173_fs_raw_mul_body_def:
  registered_case10173_fs_raw_mul_body =
    Pair
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Fst (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Snd (Var «y»))))
      (Binop Add
        (Binop Mul (Uop Fst (Var «x»)) (Uop Snd (Var «y»)))
        (Binop Mul (Uop Snd (Var «x»)) (Uop Fst (Var «y»))))
End

Definition registered_case10173_fs_first_value_body_def:
  registered_case10173_fs_first_value_body = Uop Fst (Var «first»)
End

Definition registered_case10173_fs_first_gradient_body_def:
  registered_case10173_fs_first_gradient_body = Uop Snd (Var «first»)
End

Theorem registered_case10173_fs_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_scale» =
    SOME ([],registered_case10173_fs_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_scale_squared_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_scale_squared» =
    SOME ([],registered_case10173_fs_scale_squared_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_two_scale_squared_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_two_scale_squared» =
    SOME ([],registered_case10173_fs_two_scale_squared_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_add» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_neg» =
    SOME ([«x»],registered_case10173_fs_raw_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_mul_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_mul» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_mul_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_first_value_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_first_value» =
    SOME ([«first»],registered_case10173_fs_first_value_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_first_gradient_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_first_gradient» =
    SOME ([«first»],registered_case10173_fs_first_gradient_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_scale_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_scale» []) (refs:hol_refs) =
    (M_success (Num 1000000000000),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_scale_lookup,
        registered_case10173_fs_scale_body_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_scale_squared_eval:
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_scale_squared» []) (refs:hol_refs) =
    (M_success (Num 1000000000000000000000000),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_scale_squared_lookup,
        registered_case10173_fs_scale_squared_body_def,
        registered_case10173_fs_scale_lookup,
        registered_case10173_fs_scale_body_def,
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

Theorem registered_case10173_fs_two_scale_squared_eval:
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_two_scale_squared» []) (refs:hol_refs) =
    (M_success (Num 2000000000000000000000000),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_two_scale_squared_lookup,
        registered_case10173_fs_two_scale_squared_body_def,
        registered_case10173_fs_scale_squared_lookup,
        registered_case10173_fs_scale_squared_body_def,
        registered_case10173_fs_scale_lookup,
        registered_case10173_fs_scale_body_def,
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

Theorem registered_case10173_fs_raw_add_eval:
  bounded_object_fs_raw_add left right = SOME result /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> fs [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> Cases_on `c'`
  >> Cases_on `c0'`
  >> fs [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def]
  >> rpt strip_tac
  >> gvs []
  >> Cases_on `clock`
  >> gvs
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_add_lookup,
        registered_case10173_fs_raw_add_body_def,
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

Theorem registered_case10173_fs_raw_neg_eval:
  bounded_object_fs_raw_neg value = SOME result /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_neg» [from_cv value])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `value`
  >> fs [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> fs [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_def]
  >> rpt strip_tac
  >> gvs []
  >> Cases_on `clock`
  >> gvs
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_neg_lookup,
        registered_case10173_fs_raw_neg_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_raw_mul_eval:
  bounded_object_fs_raw_mul left right = SOME result /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> fs [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_raw_mul_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> Cases_on `c'`
  >> Cases_on `c0'`
  >> fs [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_raw_mul_def]
  >> rpt strip_tac
  >> gvs []
  >> Cases_on `clock`
  >> gvs
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_mul_lookup,
        registered_case10173_fs_raw_mul_body_def,
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

Theorem registered_case10173_fs_first_value_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_value» [from_cv (Pair value gradient)])
      (refs:hol_refs) =
    (M_success (from_cv value),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_first_value_lookup,
        registered_case10173_fs_first_value_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_first_gradient_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_gradient» [from_cv (Pair value gradient)])
      (refs:hol_refs) =
    (M_success (from_cv gradient),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_first_gradient_lookup,
        registered_case10173_fs_first_gradient_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
