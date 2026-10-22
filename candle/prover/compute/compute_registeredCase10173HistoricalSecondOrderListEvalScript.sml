(*****************************************************************************
 * Registered interval-list addition for the historical second-order jet.
 *
 * This is the first recursive collection operation on the genuine box path.
 * Its statement is typed: successful bounded interval addition is refined by
 * the literal registered source program over the canonical cv list encoding.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderListEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderPrimitiveEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_interval_list_add_body_def:
  registered_case10173_fs_interval_list_add_body =
    If (Uop Ispair (Var «xs»))
      (If (Uop Ispair (Var «ys»))
        (Pair
          (App «candle_cv_fs_interval_add»
            [Uop Fst (Var «xs»);Uop Fst (Var «ys»)])
          (App «candle_cv_fs_interval_list_add»
            [Uop Snd (Var «xs»);Uop Snd (Var «ys»)]))
        (Num 0))
      (Num 0)
End

Theorem registered_case10173_fs_interval_list_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_interval_list_add» =
    SOME
      ([«xs»;«ys»],registered_case10173_fs_interval_list_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_interval_list_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_add»
        [from_cv xs;from_cv ys])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«xs»,from_cv xs);(«ys»,from_cv ys)]
        registered_case10173_fs_interval_list_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_interval_list_add_lookup]
QED

Theorem registered_case10173_fs_interval_list_add_typed_eval:
  !right result clock refs.
    bounded_interval64_list_add left right = SOME result /\
    LENGTH left + 5 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_add»
          [from_cv (bounded_interval64_object_cv_list left);
           from_cv (bounded_interval64_object_cv_list right)])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  Induct_on `left`
  >- (Cases_on `right`
      >> rpt strip_tac
      >> gvs [compute_boundedIntervalListTheory.bounded_interval64_list_add_def]
      >> rw [registered_case10173_fs_interval_list_add_unfold]
      >> simp
           [registered_case10173_fs_interval_list_add_body_def,
            compute_evalTheory.subst_def,
            compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
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
      >> gvs [compute_boundedIntervalListTheory.bounded_interval64_list_add_def])
  >> rpt strip_tac
  >> Cases_on `bounded_interval64_add h' h`
  >> gvs [compute_boundedIntervalListTheory.bounded_interval64_list_add_def]
  >> Cases_on `bounded_interval64_list_add left t`
  >> gvs [compute_boundedIntervalListTheory.bounded_interval64_list_add_def]
  >> rw [registered_case10173_fs_interval_list_add_unfold]
  >> simp
       [registered_case10173_fs_interval_list_add_body_def,
        compute_evalTheory.subst_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv h')
                 (bounded_interval64_object_cv_list left):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (bounded_interval64_object_cv h)
                 (bounded_interval64_object_cv_list t):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `bounded_interval64_object_cv x`,
            `right_result` |-> `bounded_interval64_object_cv_list x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv h'))
                 (from_cv (bounded_interval64_object_cv_list left)));
             Uop Fst
               (Pair (from_cv (bounded_interval64_object_cv h))
                 (from_cv (bounded_interval64_object_cv_list t)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [from_cv (bounded_interval64_object_cv h');
             from_cv (bounded_interval64_object_cv h)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
      >> imp_res_tac
           compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_add»
          [Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv h'))
               (from_cv (bounded_interval64_object_cv_list left)));
           Uop Snd
             (Pair (from_cv (bounded_interval64_object_cv h))
               (from_cv (bounded_interval64_object_cv_list t)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_list_add»
          [from_cv (bounded_interval64_object_cv_list left);
           from_cv (bounded_interval64_object_cv_list t)]) refs` by
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
