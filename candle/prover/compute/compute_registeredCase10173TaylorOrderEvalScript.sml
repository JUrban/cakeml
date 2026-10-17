(*****************************************************************************
 * Registered evaluator refinement for signed-pair order and magnitude.
 *
 * These operations feed interval absolute bounds in every Taylor dot
 * product.  The statements follow the bounded-object functions exactly and
 * preserve non-canonical signed pairs where the historical source does.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorOrderEval
Ancestors
  compute_registeredCase10173TaylorPrimitiveEval
Libs
  bossLib preamble

Definition registered_case10173_fs_raw_le_body_def:
  registered_case10173_fs_raw_le_body =
    Binop Less
      (Binop Add (Uop Fst (Var «x»)) (Uop Snd (Var «y»)))
      (Binop Add
        (Binop Add (Uop Fst (Var «y»)) (Uop Snd (Var «x»)))
        (Num 1))
End

Definition registered_case10173_fs_raw_max_body_def:
  registered_case10173_fs_raw_max_body =
    If (App «candle_cv_fs_raw_le» [Var «x»;Var «y»])
      (Var «y») (Var «x»)
End

Definition registered_case10173_fs_raw_abs_body_def:
  registered_case10173_fs_raw_abs_body =
    App «candle_cv_fs_raw_max»
      [Var «x»;App «candle_cv_fs_raw_neg» [Var «x»]]
End

Theorem registered_case10173_fs_raw_le_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_le» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_le_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_max_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_max» =
    SOME ([«x»;«y»],registered_case10173_fs_raw_max_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_abs_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_abs» =
    SOME ([«x»],registered_case10173_fs_raw_abs_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_le_eval:
  bounded_object_fs_raw_le left right = SOME answer /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (Num (if answer then 1 else 0)),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> fs [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> Cases_on `c'`
  >> Cases_on `c0'`
  >> fs [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_def]
  >> rpt strip_tac
  >> gvs []
  >> Cases_on `clock`
  >> gvs
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_raw_le_lookup,
        registered_case10173_fs_raw_le_body_def,
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
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_raw_max_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_max» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_raw_max_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_max_lookup]
QED

Theorem registered_case10173_compute_eval_if_bool:
  compute_eval clock ceqs condition (refs:hol_refs) =
      (M_success (Num (if answer then 1 else 0)),refs) ==>
  compute_eval clock ceqs (If condition yes_branch no_branch) refs =
    compute_eval clock ceqs
      (if answer then yes_branch else no_branch) refs
Proof
  Cases_on `answer`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_raw_max_eval:
  bounded_object_fs_raw_max left right = SOME result /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_max» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `bounded_object_fs_raw_le left right`
  >> fs [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_max_def]
  >> strip_tac
  >> gvs [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_max_def]
  >> simp [registered_case10173_fs_raw_max_unfold]
  >> simp
       [registered_case10173_fs_raw_max_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le» [from_cv left;from_cv right]) refs =
      (M_success (Num (if x then 1 else 0)),refs)` by
       (irule registered_case10173_fs_raw_le_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (If (App «candle_cv_fs_raw_le» [from_cv left;from_cv right])
          (from_cv right) (from_cv left)) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (if x then from_cv right else from_cv left) refs` by
       (irule registered_case10173_compute_eval_if_bool >> simp [])
  >> Cases_on `x`
  >> fs [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem registered_case10173_fs_raw_abs_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_abs» [from_cv value])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv value)]
        registered_case10173_fs_raw_abs_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_raw_abs_lookup]
QED

Theorem registered_case10173_fs_raw_abs_eval:
  bounded_object_fs_raw_abs value = SOME result /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_abs» [from_cv value])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `bounded_object_fs_raw_neg value`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_abs_def]
  >> Cases_on `bounded_object_fs_raw_max value x`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_abs_def]
  >> strip_tac
  >> gvs []
  >> simp [registered_case10173_fs_raw_abs_unfold]
  >> simp
       [registered_case10173_fs_raw_abs_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_max»
          [from_cv value;App «candle_cv_fs_raw_neg» [from_cv value]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_max» [from_cv value;from_cv x]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
        >> irule registered_case10173_fs_raw_neg_eval
        >> simp [])
  >> fs [registered_case10173_fs_raw_max_eval]
QED

Theorem registered_case10173_fs_raw_scale_object_eval:
  bounded_object_fs_raw_scale factor value = SOME result /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_scale»
        [from_cv (Num factor);from_cv value])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `value`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> fs
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_def]
  >> rpt strip_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_raw_scale_eval)
  >> simp []
QED

val _ = export_theory ();
