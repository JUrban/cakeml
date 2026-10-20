(*****************************************************************************
 * Registered interval-list and interval-matrix negation.
 *
 * Polynomial negation traverses the completed center gradient and expanded
 * Hessian through these two literal recursive source functions.  The typed
 * statements below refine that traversal to canonical decimal interval
 * objects without specializing it to the case-10173 fixture.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalNegListEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderMatrixEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_interval_list_neg_body_def:
  registered_case10173_fs_interval_list_neg_body =
    If (Uop Ispair (Var «items»))
      (Pair
        (App «candle_cv_fs_interval_neg» [Uop Fst (Var «items»)])
        (App «candle_cv_fs_interval_list_neg» [Uop Snd (Var «items»)]))
      (Num 0)
End

Definition registered_case10173_fs_interval_matrix_neg_body_def:
  registered_case10173_fs_interval_matrix_neg_body =
    If (Uop Ispair (Var «row_lists»))
      (Pair
        (App «candle_cv_fs_interval_list_neg»
          [Uop Fst (Var «row_lists»)])
        (App «candle_cv_fs_interval_matrix_neg»
          [Uop Snd (Var «row_lists»)]))
      (Num 0)
End

Theorem registered_case10173_fs_interval_list_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_list_neg» =
    SOME ([«items»],registered_case10173_fs_interval_list_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_matrix_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_matrix_neg» =
    SOME ([«row_lists»],registered_case10173_fs_interval_matrix_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_list_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_neg» [from_cv items])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items)]
        registered_case10173_fs_interval_list_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_list_neg_lookup]
QED

Theorem registered_case10173_fs_interval_matrix_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_neg» [from_cv rows])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«row_lists»,from_cv rows)]
        registered_case10173_fs_interval_matrix_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_interval_matrix_neg_lookup]
QED

Theorem registered_case10173_fs_interval_list_neg_typed_eval:
  !clock refs.
    LENGTH values + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_neg»
          [from_cv (bounded_interval64_object_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_interval64_object_cv_list
            (bounded_interval64_list_neg values))),refs)
Proof
  Induct_on `values`
  >- (rpt strip_tac
      >> rw [registered_case10173_fs_interval_list_neg_unfold]
      >> simp
           [registered_case10173_fs_interval_list_neg_body_def,
            compute_evalTheory.subst_def,
            compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
            compute_boundedIntervalListTheory.bounded_interval64_list_neg_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> rw [registered_case10173_fs_interval_list_neg_unfold]
  >> simp
       [registered_case10173_fs_interval_list_neg_body_def,
        compute_evalTheory.subst_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_boundedIntervalListTheory.bounded_interval64_list_neg_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv h)
                 (bounded_interval64_object_cv_list values):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
            [`left_result` |->
              `bounded_interval64_object_cv (bounded_interval64_neg h)`,
            `right_result` |->
              `bounded_interval64_object_cv_list
                (MAP bounded_interval64_neg values)`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg»
            [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv h))
                 (from_cv
                   (bounded_interval64_object_cv_list values)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg»
            [from_cv (bounded_interval64_object_cv h)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
      >> simp
           [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_neg»
          [Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv h))
               (from_cv
                 (bounded_interval64_object_cv_list values)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_neg»
          [from_cv (bounded_interval64_object_cv_list values)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> rw []
  >> PURE_REWRITE_TAC
       [GSYM compute_boundedIntervalListTheory.bounded_interval64_list_neg_def]
  >> first_x_assum (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac >- fs [arithmeticTheory.LESS_EQ]
  >> simp []
QED

Theorem registered_case10173_fs_interval_matrix_neg_typed_eval:
  !clock refs.
    SUM (MAP LENGTH rows) + LENGTH rows + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_neg»
          [from_cv (bounded_interval64_object_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_interval64_object_cv_matrix
            (MAP bounded_interval64_list_neg rows))),refs)
Proof
  Induct_on `rows`
  >- (rpt strip_tac
      >> rw [registered_case10173_fs_interval_matrix_neg_unfold]
      >> simp
           [registered_case10173_fs_interval_matrix_neg_body_def,
            compute_evalTheory.subst_def,
            compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> rw [registered_case10173_fs_interval_matrix_neg_unfold]
  >> simp
       [registered_case10173_fs_interval_matrix_neg_body_def,
        compute_evalTheory.subst_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv_list h)
                 (bounded_interval64_object_cv_matrix rows):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |->
              `bounded_interval64_object_cv_list
                (bounded_interval64_list_neg h)`,
            `right_result` |->
              `bounded_interval64_object_cv_matrix
                (MAP bounded_interval64_list_neg rows)`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_neg»
            [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv_list h))
                 (from_cv
                   (bounded_interval64_object_cv_matrix rows)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_neg»
            [from_cv (bounded_interval64_object_cv_list h)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
      >> rw []
      >> irule registered_case10173_fs_interval_list_neg_typed_eval
      >> fs [arithmeticTheory.LESS_EQ])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_neg»
          [Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv_list h))
               (from_cv
                 (bounded_interval64_object_cv_matrix rows)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_neg»
          [from_cv (bounded_interval64_object_cv_matrix rows)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> rw []
  >> first_x_assum (qspecl_then [`clock - 1`,`refs`] mp_tac)
  >> impl_tac >- fs [arithmeticTheory.LESS_EQ]
  >> simp []
QED

val _ = export_theory ();
