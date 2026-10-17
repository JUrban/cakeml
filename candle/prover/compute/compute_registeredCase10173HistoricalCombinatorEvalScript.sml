(*****************************************************************************
 * Registered evaluator semantics for small historical center combinators.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalCombinatorEval
Ancestors
  compute_registeredCase10173HistoricalBasicEval
Libs
  bossLib preamble

Definition registered_case10173_fs_hist_replace_three_body_def:
  registered_case10173_fs_hist_replace_three_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_interval_lookup» [Num 0;Var «items»];
       App «candle_cv_fs_interval_lookup» [Num 1;Var «items»];
       App «candle_cv_fs_interval_lookup» [Num 2;Var «items»];
       Var «value»;
       App «candle_cv_fs_interval_lookup» [Num 4;Var «items»];
       App «candle_cv_fs_interval_lookup» [Num 5;Var «items»]]
End

Theorem registered_case10173_fs_hist_replace_three_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_replace_three» =
    SOME
      ([«items»;«value»],
       registered_case10173_fs_hist_replace_three_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_compute_eval_app6_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) /\
  compute_eval clock ceqs argument6 refs =
      (M_success (from_cv result6),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;argument5;argument6]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;
         from_cv result4;from_cv result5;from_cv result6]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 6`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_lookup_num_object_list_eval:
  !index values clock refs.
    index < LENGTH values /\
    index + 2 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num index;
           from_cv (bounded_interval64_object_cv_list values)])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv (EL index values))),refs)
Proof
  rpt strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
  >> simp []
QED

Theorem registered_case10173_fs_hist_replace_three_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_replace_three»
        [from_cv items;from_cv value]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«items»,from_cv items);(«value»,from_cv value)]
        registered_case10173_fs_hist_replace_three_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_hist_replace_three_lookup]
QED

Theorem registered_case10173_fs_hist_replace_three_six_eval:
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_replace_three»
        [from_cv
          (bounded_interval64_object_cv_list [v0;v1;v2;v3;v4;v5]);
         from_cv (bounded_interval64_object_cv replacement)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv_list
          [v0;v1;v2;replacement;v4;v5])),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_hist_replace_three_unfold]
  >> simp
       [registered_case10173_fs_hist_replace_three_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num 0;
           from_cv (bounded_interval64_object_cv_list
             [v0;v1;v2;v3;v4;v5])]) refs =
      (M_success (from_cv (bounded_interval64_object_cv v0)),refs)` by
       (irule
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL
              [`0`,`[v0;v1;v2;v3;v4;v5]`,`clock - 1`,`refs`]
              registered_case10173_fs_interval_lookup_num_object_list_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num 1;
           from_cv (bounded_interval64_object_cv_list
             [v0;v1;v2;v3;v4;v5])]) refs =
      (M_success (from_cv (bounded_interval64_object_cv v1)),refs)` by
       (irule
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL
              [`1`,`[v0;v1;v2;v3;v4;v5]`,`clock - 1`,`refs`]
              registered_case10173_fs_interval_lookup_num_object_list_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num 2;
           from_cv (bounded_interval64_object_cv_list
             [v0;v1;v2;v3;v4;v5])]) refs =
      (M_success (from_cv (bounded_interval64_object_cv v2)),refs)` by
       (irule
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL
              [`2`,`[v0;v1;v2;v3;v4;v5]`,`clock - 1`,`refs`]
              registered_case10173_fs_interval_lookup_num_object_list_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num 4;
           from_cv (bounded_interval64_object_cv_list
             [v0;v1;v2;v3;v4;v5])]) refs =
      (M_success (from_cv (bounded_interval64_object_cv v4)),refs)` by
       (irule
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL
              [`4`,`[v0;v1;v2;v3;v4;v5]`,`clock - 1`,`refs`]
              registered_case10173_fs_interval_lookup_num_object_list_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_lookup»
          [Num 5;
           from_cv (bounded_interval64_object_cv_list
             [v0;v1;v2;v3;v4;v5])]) refs =
      (M_success (from_cv (bounded_interval64_object_cv v5)),refs)` by
       (irule
          (SIMP_RULE (srw_ss()) []
            (Q.SPECL
              [`5`,`[v0;v1;v2;v3;v4;v5]`,`clock - 1`,`refs`]
              registered_case10173_fs_interval_lookup_num_object_list_eval))
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_six»
          [App «candle_cv_fs_interval_lookup»
            [Num 0;
             from_cv (bounded_interval64_object_cv_list
               [v0;v1;v2;v3;v4;v5])];
           App «candle_cv_fs_interval_lookup»
            [Num 1;
             from_cv (bounded_interval64_object_cv_list
               [v0;v1;v2;v3;v4;v5])];
           App «candle_cv_fs_interval_lookup»
            [Num 2;
             from_cv (bounded_interval64_object_cv_list
               [v0;v1;v2;v3;v4;v5])];
           from_cv (bounded_interval64_object_cv replacement);
           App «candle_cv_fs_interval_lookup»
            [Num 4;
             from_cv (bounded_interval64_object_cv_list
               [v0;v1;v2;v3;v4;v5])];
           App «candle_cv_fs_interval_lookup»
            [Num 5;
             from_cv (bounded_interval64_object_cv_list
               [v0;v1;v2;v3;v4;v5])]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_six»
          [from_cv (bounded_interval64_object_cv v0);
           from_cv (bounded_interval64_object_cv v1);
           from_cv (bounded_interval64_object_cv v2);
           from_cv (bounded_interval64_object_cv replacement);
           from_cv (bounded_interval64_object_cv v4);
           from_cv (bounded_interval64_object_cv v5)]) refs` by
       (irule registered_case10173_compute_eval_app6_argument_results
        >> simp
             [registered_case10173_fs_interval_lookup_num_object_list_eval,
              compute_execProofTheory.compute_eval_from_cv]
        >> intLib.ARITH_TAC)
  >> rw []
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Theorem registered_case10173_fs_hist_replace_three_object_eval:
  !values replacement result clock refs.
    bounded_historical_replace_three values replacement = SOME result /\
    8 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_replace_three»
          [from_cv (bounded_interval64_object_cv_list values);
           from_cv (bounded_interval64_object_cv replacement)])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> fs
       [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_replace_three_def]
  >> every_case_tac
  >> gvs [registered_case10173_fs_hist_replace_three_six_eval]
QED

val _ = export_theory ();
