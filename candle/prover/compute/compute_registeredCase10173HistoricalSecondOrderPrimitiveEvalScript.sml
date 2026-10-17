(*****************************************************************************
 * Structural registered evaluators used by the historical second-order jet.
 *
 * These constructors and projections carry no numerical content.  Keeping
 * their exact evaluator facts in a small theory prevents the later Hessian
 * refinements from repeatedly unfolding tuple representation details.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderPrimitiveEval
Ancestors
  compute_registeredCase10173HistoricalFirstOrderCenterEval
  compute_registeredCase10173HistCompletionEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_second_make_body_def:
  registered_case10173_fs_hist_second_make_body =
    Pair (Var «value») (Pair (Var «gradient») (Var «hessian»))
End

Definition registered_case10173_fs_hist_second_gradient_body_def:
  registered_case10173_fs_hist_second_gradient_body =
    Uop Fst (Uop Snd (Var «second»))
End

Definition registered_case10173_fs_angle_matrix_lookup_body_def:
  registered_case10173_fs_angle_matrix_lookup_body =
    App «candle_cv_fs_interval_lookup»
      [Var «colindex»;
       App «candle_cv_fs_interval_lookup»
         [Var «rowindex»;Var «matrixvalue»]]
End

Theorem registered_case10173_fs_hist_second_make_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_make» =
    SOME
      ([«value»;«gradient»;«hessian»],
       registered_case10173_fs_hist_second_make_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_second_gradient_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_gradient» =
    SOME
      ([«second»],registered_case10173_fs_hist_second_gradient_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_matrix_lookup_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_matrix_lookup» =
    SOME
      ([«rowindex»;«colindex»;«matrixvalue»],
       registered_case10173_fs_angle_matrix_lookup_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_matrix_lookup_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_matrix_lookup»
        [from_cv rowindex;from_cv colindex;from_cv matrixvalue])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);
         («colindex»,from_cv colindex);
         («matrixvalue»,from_cv matrixvalue)]
        registered_case10173_fs_angle_matrix_lookup_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_hist_compute_eval_literal_app3
  >> simp [registered_case10173_fs_angle_matrix_lookup_lookup]
QED

Theorem registered_case10173_fs_hist_second_make_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_make»
        [from_cv value;from_cv gradient;from_cv hessian])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (value:cv) (Pair (gradient:cv) (hessian:cv)) : cv)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_second_make_lookup,
        registered_case10173_fs_hist_second_make_body_def,
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

Theorem registered_case10173_fs_hist_second_gradient_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_gradient»
        [from_cv
          (Pair (value:cv) (Pair (gradient:cv) (hessian:cv)) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv gradient),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_second_gradient_lookup,
        registered_case10173_fs_hist_second_gradient_body_def,
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

Theorem registered_case10173_object_matrix_as_cv_list:
  bounded_interval64_object_cv_matrix rows =
    registered_case10173_cv_list
      (MAP bounded_interval64_object_cv_list rows)
Proof
  Induct_on `rows`
  >> simp
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_fs_angle_matrix_lookup_typed_eval:
  rowindex < LENGTH rows /\
  colindex < LENGTH (EL rowindex rows) /\
  rowindex + 3 < clock /\
  colindex + 3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_matrix_lookup»
        [from_cv (Num rowindex);from_cv (Num colindex);
         from_cv (bounded_interval64_object_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (EL colindex (EL rowindex rows)))),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_angle_matrix_lookup_unfold]
  >> simp
       [registered_case10173_fs_angle_matrix_lookup_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num rowindex;
           from_cv (bounded_interval64_object_cv_matrix rows)]) refs =
      (M_success
        (from_cv
          (bounded_interval64_object_cv_list
            (EL rowindex rows))),refs)` by
       (rw [registered_case10173_object_matrix_as_cv_list]
        >> mp_tac
             (Q.SPECL
               [`rowindex`,
                `MAP bounded_interval64_object_cv_list rows`,
                `clock - 1`,`refs`]
               compute_registeredCase10173HistoricalCVectorEvalTheory.registered_case10173_fs_interval_lookup_cv_list_eval)
        >> impl_tac >- (simp [] >> intLib.ARITH_TAC)
        >> simp [EL_MAP])
  >> `(Num colindex:compute_exp) = from_cv (Num colindex:cv)` by
       simp [compute_execTheory.from_cv_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Num colindex) refs =
      (M_success (from_cv (Num colindex)),refs)` by
       metis_tac [compute_execProofTheory.compute_eval_from_cv]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num colindex;
           App «candle_cv_fs_interval_lookup»
             [Num rowindex;
              from_cv (bounded_interval64_object_cv_matrix rows)]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [from_cv (Num colindex);
           from_cv
             (bounded_interval64_object_cv_list
               (EL rowindex rows))]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac >- first_assum ACCEPT_TAC
        >> first_assum ACCEPT_TAC)
  >> qpat_x_assum
       `compute_eval _ _
          (App «candle_cv_fs_interval_lookup»
            [Num colindex;App «candle_cv_fs_interval_lookup» _]) _ =
        compute_eval _ _ _ _`
       (fn th => once_rewrite_tac [th])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_second_hessian_typed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_hessian»
        [from_cv
          (Pair
            (bounded_interval64_object_cv value)
            (Pair
              (bounded_interval64_object_cv_list gradient)
              (bounded_interval64_object_cv_list hessian)))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_list hessian)),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_second_gradient_typed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_gradient»
        [from_cv
          (Pair
            (bounded_interval64_object_cv value)
            (Pair
              (bounded_interval64_object_cv_list gradient)
              (bounded_interval64_object_cv_list hessian)))])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_list gradient)),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_hist_second_gradient_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_second_make_typed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_make»
        [from_cv (bounded_interval64_object_cv value);
         from_cv (bounded_interval64_object_cv_list gradient);
         from_cv (bounded_interval64_object_cv_list hessian)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv value)
          (Pair
            (bounded_interval64_object_cv_list gradient)
            (bounded_interval64_object_cv_list hessian)))),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_hist_second_make_eval
  >> simp []
QED

val _ = export_theory ();
