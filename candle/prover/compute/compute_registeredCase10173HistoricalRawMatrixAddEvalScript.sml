(*****************************************************************************
 * Registered evaluator semantics for historical raw interval-matrix addition.
 *
 * The product rule combines four unrounded Hessian contributions before one
 * outward rounding pass.  This layer follows the literal recursive matrix
 * source operation over canonical raw cv rows.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalRawMatrixAddEval
Ancestors
  compute_registeredCase10173HistoricalRawListAddEval
  compute_registeredCase10173HistoricalSecondOrderMatrixScaleEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_raw_interval_matrix_add_body_def:
  registered_case10173_fs_raw_interval_matrix_add_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (Pair
          (App «candle_cv_fs_raw_interval_list_add»
            [Uop Fst (Var «xs»);Uop Fst (Var «ys»)])
          (App «candle_cv_fs_raw_interval_matrix_add»
            [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]))
        (Num 0))
      (Num 0)
End

Definition registered_case10173_fs_raw_interval_matrix_add_object_def:
  registered_case10173_fs_raw_interval_matrix_add_object
      ([]:cv list list) [] = SOME [] /\
  registered_case10173_fs_raw_interval_matrix_add_object
      (left::left_rest) (right::right_rest) =
    (case registered_case10173_fs_raw_interval_list_add_object left right of
     | NONE => NONE
     | SOME row =>
       case registered_case10173_fs_raw_interval_matrix_add_object
         left_rest right_rest of
       | NONE => NONE
       | SOME rows => SOME (row::rows)) /\
  registered_case10173_fs_raw_interval_matrix_add_object _ _ = NONE
End

Theorem registered_case10173_fs_raw_interval_matrix_add_object_shape:
  !right result.
    registered_case10173_fs_raw_interval_matrix_add_object
      left right = SOME result ==>
    MAP LENGTH left = MAP LENGTH right /\
    MAP LENGTH result = MAP LENGTH left
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw [registered_case10173_fs_raw_interval_matrix_add_object_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_length
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_fs_raw_interval_matrix_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_matrix_add» =
    SOME
      ([«xs»;«ys»],
       registered_case10173_fs_raw_interval_matrix_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_matrix_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_add»
        [from_cv (registered_case10173_cv_matrix left);
         from_cv (registered_case10173_cv_matrix right)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«xs»,from_cv (registered_case10173_cv_matrix left));
         («ys»,from_cv (registered_case10173_cv_matrix right))]
        registered_case10173_fs_raw_interval_matrix_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_matrix_add_lookup]
QED

Theorem registered_case10173_fs_raw_interval_matrix_add_object_eval:
  !right result clock refs.
    registered_case10173_fs_raw_interval_matrix_add_object
        left right = SOME result /\
    SUM (MAP LENGTH left) + LENGTH left + 5 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_add»
          [from_cv (registered_case10173_cv_matrix left);
           from_cv (registered_case10173_cv_matrix right)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_matrix result)),refs)
Proof
  Induct_on `left`
  >- (Cases_on `right`
      >> rpt strip_tac
      >> gvs [registered_case10173_fs_raw_interval_matrix_add_object_def]
      >> rw [registered_case10173_fs_raw_interval_matrix_add_unfold]
      >> simp
           [registered_case10173_fs_raw_interval_matrix_add_body_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
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
      >> gvs [registered_case10173_fs_raw_interval_matrix_add_object_def])
  >> rpt strip_tac
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_add_object h' h`
  >> gvs [registered_case10173_fs_raw_interval_matrix_add_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_matrix_add_object left t`
  >> gvs [registered_case10173_fs_raw_interval_matrix_add_object_def]
  >> rw [registered_case10173_fs_raw_interval_matrix_add_unfold]
  >> simp
       [registered_case10173_fs_raw_interval_matrix_add_body_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_cons,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (registered_case10173_cv_list h')
                 (registered_case10173_cv_matrix left):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (registered_case10173_cv_list h)
                 (registered_case10173_cv_matrix t):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `registered_case10173_cv_list x`,
            `right_result` |-> `registered_case10173_cv_matrix x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_add»
            [Uop Fst
               (Pair (from_cv (registered_case10173_cv_list h'))
                 (from_cv (registered_case10173_cv_matrix left)));
             Uop Fst
               (Pair (from_cv (registered_case10173_cv_list h))
                 (from_cv (registered_case10173_cv_matrix t)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_add»
            [from_cv (registered_case10173_cv_list h');
             from_cv (registered_case10173_cv_list h)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_add»
          [Uop Snd
             (Pair (from_cv (registered_case10173_cv_list h'))
               (from_cv (registered_case10173_cv_matrix left)));
           Uop Snd
             (Pair (from_cv (registered_case10173_cv_list h))
               (from_cv (registered_case10173_cv_matrix t)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_add»
          [from_cv (registered_case10173_cv_matrix left);
           from_cv (registered_case10173_cv_matrix t)]) refs` by
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
