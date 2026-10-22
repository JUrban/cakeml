(*****************************************************************************
 * Registered evaluator semantics for the historical delta_x4 gradient.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4GradientEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4ValueEval
  compute_registeredCase10173HistoricalTupleEval
  compute_registeredCase10173TaylorOrderEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_interval_raw_scale_object_def:
  registered_case10173_fs_interval_raw_scale_object factor
      (Pair lower upper : cv) =
    (case bounded_object_fs_raw_scale factor lower of
     | NONE => NONE
     | SOME lower' =>
       case bounded_object_fs_raw_scale factor upper of
       | NONE => NONE
       | SOME upper' => SOME (Pair lower' upper')) /\
  registered_case10173_fs_interval_raw_scale_object factor _ = NONE
End

Theorem registered_case10173_fs_angle_interval_scale_object_eval:
  registered_case10173_fs_interval_raw_scale_object factor source =
      SOME result /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [from_cv (Num factor);from_cv source]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `source`
  >- simp [registered_case10173_fs_interval_raw_scale_object_def]
  >> rw [registered_case10173_fs_interval_raw_scale_object_def]
  >> every_case_tac
  >> gvs []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«factor»,from_cv (Num factor));
             («value»,from_cv (Pair c c0))]
            registered_case10173_fs_angle_interval_scale_body) refs`
  >> conj_tac
  >- (simp
        [Once compute_evalTheory.compute_eval_def,
         compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_angle_interval_scale_lookup,
         compute_evalTheory.option_def,
         compute_evalTheory.check_def,
         ml_monadBaseTheory.st_ex_bind_def,
         ml_monadBaseTheory.st_ex_ignore_bind_def,
         ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_execProofTheory.compute_eval_from_cv,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_ignore_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp
       [compute_registeredCase10173RootInputsEvalTheory.registered_case10173_fs_angle_interval_scale_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_raw_scale»
                [from_cv (Num factor);from_cv c]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> simp
               [compute_execTheory.from_cv_def,
                compute_execProofTheory.compute_eval_from_cv,
                compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
                compute_evalTheory.compute_eval_def,
                ml_monadBaseTheory.st_ex_return_def])
      >> irule
           compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_scale»
            [from_cv (Num factor);from_cv c0]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> simp
           [compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
            compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> irule
       compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_interval_scale_neg_two_object_def:
  registered_case10173_fs_interval_scale_neg_two_object source =
    case registered_case10173_fs_interval_raw_scale_object 2 source of
    | NONE => NONE
    | SOME twice => bounded_object_fs_interval_neg twice
End

Definition registered_case10173_fs_angle_interval_scale_neg_two_body_def:
  registered_case10173_fs_angle_interval_scale_neg_two_body =
    App «candle_cv_fs_interval_neg»
      [App «candle_cv_fs_angle_interval_scale»
        [Num 2;Var «value»]]
End

Theorem registered_case10173_fs_angle_interval_scale_neg_two_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_interval_scale_neg_two» =
    SOME
      ([«value»],
       registered_case10173_fs_angle_interval_scale_neg_two_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_interval_scale_neg_two_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale_neg_two»
        [from_cv source]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«value»,from_cv source)]
        registered_case10173_fs_angle_interval_scale_neg_two_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_angle_interval_scale_neg_two_lookup]
QED

Theorem registered_case10173_fs_angle_interval_scale_neg_two_object_eval:
  registered_case10173_fs_interval_scale_neg_two_object source =
      SOME result /\
  9 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale_neg_two»
        [from_cv source]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [registered_case10173_fs_interval_scale_neg_two_object_def]
  >> every_case_tac
  >> gvs []
  >> simp [registered_case10173_fs_angle_interval_scale_neg_two_unfold]
  >> simp
       [registered_case10173_fs_angle_interval_scale_neg_two_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv x]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_angle_interval_scale_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_three_sum_argument_results:
  registered_case10173_fs_interval_sum_object [r0;r1;r2] = SOME result /\
  8 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) = (M_success (from_cv r0),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs = (M_success (from_cv r1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs = (M_success (from_cv r2),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_hist_three»
          [argument0;argument1;argument2]]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_sum»
            [from_cv
              (registered_case10173_cv_list [r0;r1;r2])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_hist_three»
                [from_cv r0;from_cv r1;from_cv r2]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_three_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_interval_sum_object_list_eval
  >> simp []
QED

Definition registered_case10173_fs_hist_delta_x4_gradient_body_def:
  registered_case10173_fs_hist_delta_x4_gradient_body =
    Let «x0»
      (App «candle_cv_fs_interval_lookup»
        [Num 0;Var «environment»])
      (Let «x1»
        (App «candle_cv_fs_interval_lookup»
          [Num 1;Var «environment»])
        (Let «x2»
          (App «candle_cv_fs_interval_lookup»
            [Num 2;Var «environment»])
          (Let «x3»
            (App «candle_cv_fs_interval_lookup»
              [Num 3;Var «environment»])
            (Let «x4»
              (App «candle_cv_fs_interval_lookup»
                [Num 4;Var «environment»])
              (Let «x5»
                (App «candle_cv_fs_interval_lookup»
                  [Num 5;Var «environment»])
                (App «candle_cv_fs_angle_six»
                  [App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_angle_six»
                      [App «candle_cv_fs_angle_interval_scale_neg_two»
                         [Var «x0»];
                       Var «x1»;Var «x2»;
                       App «candle_cv_fs_angle_interval_scale_neg_two»
                         [Var «x3»];
                       Var «x4»;Var «x5»]];
                   App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_hist_three»
                      [Var «x0»;
                       App «candle_cv_fs_interval_neg» [Var «x2»];
                       Var «x4»]];
                   App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_hist_three»
                      [Var «x0»;
                       App «candle_cv_fs_interval_neg» [Var «x1»];
                       Var «x5»]];
                   App «candle_cv_fs_angle_interval_scale_neg_two»
                     [Var «x0»];
                   App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_hist_three»
                      [Var «x0»;Var «x1»;
                       App «candle_cv_fs_interval_neg» [Var «x5»]]];
                   App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_hist_three»
                      [Var «x0»;Var «x2»;
                       App «candle_cv_fs_interval_neg» [Var «x4»]]]]))))))
End

Theorem registered_case10173_fs_hist_delta_x4_gradient_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_x4_gradient» =
    SOME
      ([«environment»],
       registered_case10173_fs_hist_delta_x4_gradient_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_gradient_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_gradient»
        [from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_delta_x4_gradient_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_x4_gradient_lookup]
QED

Theorem registered_case10173_fs_hist_delta_x4_gradient_trace_eval:
  registered_case10173_fs_interval_scale_neg_two_object x0 =
      SOME negative_two_x0 /\
  registered_case10173_fs_interval_scale_neg_two_object x3 =
      SOME negative_two_x3 /\
  bounded_object_fs_interval_neg x2 = SOME negative_x2 /\
  bounded_object_fs_interval_neg x1 = SOME negative_x1 /\
  bounded_object_fs_interval_neg x5 = SOME negative_x5 /\
  bounded_object_fs_interval_neg x4 = SOME negative_x4 /\
  registered_case10173_fs_interval_sum_object
      [negative_two_x0;x1;x2;negative_two_x3;x4;x5] = SOME g0 /\
  registered_case10173_fs_interval_sum_object
      [x0;negative_x2;x4] = SOME g1 /\
  registered_case10173_fs_interval_sum_object
      [x0;negative_x1;x5] = SOME g2 /\
  registered_case10173_fs_interval_sum_object
      [x0;x1;negative_x5] = SOME g4 /\
  registered_case10173_fs_interval_sum_object
      [x0;x2;negative_x4] = SOME g5 /\
  25 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_gradient»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_cv_list
          [g0;g1;g2;negative_two_x0;g4;g5])),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_delta_x4_gradient_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_x4_gradient_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x0`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x1`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x2`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x3`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x4`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x5`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 7)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv g0;from_cv g1;from_cv g2;
             from_cv negative_two_x0;from_cv g4;from_cv g5]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >- (irule registered_case10173_fs_angle_six_sum_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> qexistsl_tac
               [`negative_two_x0`,`x1`,`x2`,
                `negative_two_x3`,`x4`,`x5`]
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                registered_case10173_fs_angle_interval_scale_neg_two_object_eval]
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_hist_three_sum_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> qexistsl_tac [`x0`,`negative_x2`,`x4`]
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_hist_three_sum_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> qexistsl_tac [`x0`,`negative_x1`,`x5`]
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_angle_interval_scale_neg_two_object_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_hist_three_sum_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> qexistsl_tac [`x0`,`x1`,`negative_x5`]
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_fs_hist_three_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`x0`,`x2`,`negative_x4`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
