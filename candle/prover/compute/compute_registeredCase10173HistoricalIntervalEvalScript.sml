(*****************************************************************************
 * Registered evaluator semantics for the historical interval primitives.
 *
 * These operations are shared by both remaining dihedral refinements.  The
 * statements deliberately use the bounded-object interface so the exact
 * decimal proofs can be composed without replaying the generic evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalIntervalEval
Ancestors
  compute_registeredCase10173TaylorRoundEval
Libs
  bossLib preamble

Definition registered_case10173_fs_canonical_body_def:
  registered_case10173_fs_canonical_body =
    If (Binop Less (Uop Fst (Var «x»)) (Uop Snd (Var «x»)))
      (Pair (Num 0)
        (Binop Sub (Uop Snd (Var «x»)) (Uop Fst (Var «x»))))
      (Pair
        (Binop Sub (Uop Fst (Var «x»)) (Uop Snd (Var «x»)))
        (Num 0))
End

Definition registered_case10173_fs_add_body_def:
  registered_case10173_fs_add_body =
    App «candle_cv_fs_canonical»
      [App «candle_cv_fs_raw_add» [Var «x»;Var «y»]]
End

Definition registered_case10173_fs_neg_body_def:
  registered_case10173_fs_neg_body =
    App «candle_cv_fs_raw_neg» [Var «x»]
End

Definition registered_case10173_fs_interval_neg_body_def:
  registered_case10173_fs_interval_neg_body =
    Pair
      (App «candle_cv_fs_neg» [Uop Snd (Var «i»)])
      (App «candle_cv_fs_neg» [Uop Fst (Var «i»)])
End

Definition registered_case10173_fs_interval_add_body_def:
  registered_case10173_fs_interval_add_body =
    Pair
      (App «candle_cv_fs_add»
        [Uop Fst (Var «x»);Uop Fst (Var «y»)])
      (App «candle_cv_fs_add»
        [Uop Snd (Var «x»);Uop Snd (Var «y»)])
End

Theorem registered_case10173_fs_canonical_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_canonical» =
    SOME ([«x»],registered_case10173_fs_canonical_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_add» =
    SOME ([«x»;«y»],registered_case10173_fs_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_neg» =
    SOME ([«x»],registered_case10173_fs_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_neg» =
    SOME ([«i»],registered_case10173_fs_interval_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_add» =
    SOME ([«x»;«y»],registered_case10173_fs_interval_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_canonical_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_canonical» [from_cv source])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv source)]
        registered_case10173_fs_canonical_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_canonical_lookup]
QED

Theorem registered_case10173_fs_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_add_lookup]
QED

Theorem registered_case10173_fs_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_neg» [from_cv source]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv source)] registered_case10173_fs_neg_body)
      refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_neg_lookup]
QED

Theorem registered_case10173_fs_interval_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv source])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«i»,from_cv source)]
        registered_case10173_fs_interval_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_neg_lookup]
QED

Theorem registered_case10173_fs_interval_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv left);(«y»,from_cv right)]
        registered_case10173_fs_interval_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_interval_add_lookup]
QED

Theorem registered_case10173_fs_canonical_eval:
  bounded_object_fs_canonical source = SOME result /\
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_canonical» [from_cv source])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def]
  >> Cases_on `n < n'`
  >> rpt strip_tac
  >> gvs [compute_execTheory.from_cv_def]
  >> Cases_on `clock`
  >> gvs
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_canonical_lookup,
        registered_case10173_fs_canonical_body_def,
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
QED

Theorem registered_case10173_fs_add_eval:
  bounded_object_fs_add left right = SOME result /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [registered_case10173_fs_add_unfold,
        registered_case10173_fs_add_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_canonical»
          [App «candle_cv_fs_raw_add» [from_cv left;from_cv right]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_canonical» [from_cv x]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> irule
             compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval
        >> simp [])
  >> rw []
  >> irule registered_case10173_fs_canonical_eval
  >> simp []
QED

Theorem registered_case10173_fs_neg_eval:
  bounded_object_fs_neg source = SOME result /\
  1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_neg» [from_cv source]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [compute_boundedObjectDecimalAddTheory.bounded_object_fs_neg_def]
  >> simp
       [registered_case10173_fs_neg_unfold,
        registered_case10173_fs_neg_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_eval)
  >> simp []
QED

Theorem registered_case10173_fs_interval_neg_eval:
  bounded_object_fs_interval_neg source = SOME result /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv source])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >> rw
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`source` |-> `Pair c c0`]
            registered_case10173_fs_interval_neg_unfold))]
  >> simp
       [registered_case10173_fs_interval_neg_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_neg»
          [Uop Snd (Pair (from_cv c) (from_cv c0))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg»
             [Uop Snd (Pair (from_cv c) (from_cv c0))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg» [from_cv c0]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> fs [registered_case10173_fs_neg_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_neg»
          [Uop Fst (Pair (from_cv c) (from_cv c0))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg»
             [Uop Fst (Pair (from_cv c) (from_cv c0))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_neg» [from_cv c]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs [registered_case10173_fs_neg_eval])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp []
QED

Theorem registered_case10173_fs_interval_add_eval:
  bounded_object_fs_interval_add left right = SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [(SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`left` |-> `Pair c c0`, `right` |-> `Pair c' c0'`]
            registered_case10173_fs_interval_add_unfold))]
  >> simp
       [registered_case10173_fs_interval_add_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_add»
          [Uop Fst (Pair (from_cv c) (from_cv c0));
           Uop Fst (Pair (from_cv c') (from_cv c0'))]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add»
             [Uop Fst (Pair (from_cv c) (from_cv c0));
              Uop Fst (Pair (from_cv c') (from_cv c0'))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add» [from_cv c;from_cv c']) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> fs [registered_case10173_fs_add_eval])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_add»
          [Uop Snd (Pair (from_cv c) (from_cv c0));
           Uop Snd (Pair (from_cv c') (from_cv c0'))]) refs =
      (M_success (from_cv x),refs)` by
       (`compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add»
             [Uop Snd (Pair (from_cv c) (from_cv c0));
              Uop Snd (Pair (from_cv c') (from_cv c0'))]) refs =
         compute_eval (clock - 1)
           registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_add» [from_cv c0;from_cv c0']) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp
                [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> fs [registered_case10173_fs_add_eval])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> simp []
QED

val _ = export_theory ();
