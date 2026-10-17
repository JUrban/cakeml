(*****************************************************************************
 * Registered interval-matrix addition for the historical second-order jet.
 *
 * The fuel bound charges the total number of row entries plus the outer list
 * depth.  It is intentionally structural and reusable by all six-dimensional
 * Hessian assemblies, rather than being specialized to the genuine fixture.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderMatrixEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderListEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_interval_matrix_add_body_def:
  registered_case10173_fs_interval_matrix_add_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (Pair
          (App «candle_cv_fs_interval_list_add»
            [Uop Fst (Var «xs»);Uop Fst (Var «ys»)])
          (App «candle_cv_fs_interval_matrix_add»
            [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]))
        (Num 0))
      (Num 0)
End

Theorem registered_case10173_fs_interval_matrix_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_matrix_add» =
    SOME
      ([«xs»;«ys»],registered_case10173_fs_interval_matrix_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_matrix_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_add»
        [from_cv xs;from_cv ys])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«xs»,from_cv xs);(«ys»,from_cv ys)]
        registered_case10173_fs_interval_matrix_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_interval_matrix_add_lookup]
QED

Theorem registered_case10173_fs_interval_matrix_add_typed_eval:
  !right result clock refs.
    bounded_interval64_matrix_add left right = SOME result /\
    SUM (MAP LENGTH left) + LENGTH left + 5 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_add»
          [from_cv (bounded_interval64_object_cv_matrix left);
           from_cv (bounded_interval64_object_cv_matrix right)])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_matrix result)),refs)
Proof
  Induct_on `left`
  >- (Cases_on `right`
      >> rpt strip_tac
      >> gvs
           [compute_boundedObjectTaylorStateDecimalTheory.bounded_interval64_matrix_add_def]
      >> rw [registered_case10173_fs_interval_matrix_add_unfold]
      >> simp
           [registered_case10173_fs_interval_matrix_add_body_def,
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
  >> Cases_on `right`
  >- (rpt strip_tac
      >> gvs
           [compute_boundedObjectTaylorStateDecimalTheory.bounded_interval64_matrix_add_def])
  >> rpt strip_tac
  >> Cases_on `bounded_interval64_list_add h' h`
  >> gvs
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_interval64_matrix_add_def]
  >> Cases_on `bounded_interval64_matrix_add left t`
  >> gvs
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_interval64_matrix_add_def]
  >> rw [registered_case10173_fs_interval_matrix_add_unfold]
  >> simp
       [registered_case10173_fs_interval_matrix_add_body_def,
        compute_evalTheory.subst_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv_list h')
                 (bounded_interval64_object_cv_matrix left):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv_list h)
                 (bounded_interval64_object_cv_matrix t):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `bounded_interval64_object_cv_list x`,
            `right_result` |-> `bounded_interval64_object_cv_matrix x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_add»
            [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv_list h'))
                 (from_cv (bounded_interval64_object_cv_matrix left)));
             Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv_list h))
                 (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_add»
            [from_cv (bounded_interval64_object_cv_list h');
             from_cv (bounded_interval64_object_cv_list h)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule registered_case10173_fs_interval_list_add_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_add»
          [Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv_list h'))
               (from_cv (bounded_interval64_object_cv_matrix left)));
           Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv_list h))
               (from_cv (bounded_interval64_object_cv_matrix t)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_matrix_add»
          [from_cv (bounded_interval64_object_cv_matrix left);
           from_cv (bounded_interval64_object_cv_matrix t)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
        >> intLib.ARITH_TAC)
  >> rw []
  >> first_x_assum irule
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
