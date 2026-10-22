(*****************************************************************************
 * Registered evaluator semantics for the historical delta_x4 center value.
 *
 * The source uses two literal six-entry recursive sums.  The trace theorem
 * keeps their source order explicit instead of silently reassociating bounded
 * additions.  Its premises are exactly the successful bounded-object
 * operations needed by the registered program.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4ValueEval
Ancestors
  compute_registeredCase10173HistoricalCVectorEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_delta_x4_value_body_def:
  registered_case10173_fs_hist_delta_x4_value_body =
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
                (Let «linear»
                  (App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_angle_six»
                      [App «candle_cv_fs_interval_neg» [Var «x0»];
                       Var «x1»;Var «x2»;
                       App «candle_cv_fs_interval_neg» [Var «x3»];
                       Var «x4»;Var «x5»]])
                  (App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_angle_six»
                      [App «candle_cv_fs_interval_neg»
                        [App «candle_cv_fs_angle_interval_mul»
                          [Var «x1»;Var «x2»]];
                       App «candle_cv_fs_interval_neg»
                        [App «candle_cv_fs_angle_interval_mul»
                          [Var «x0»;Var «x3»]];
                       App «candle_cv_fs_angle_interval_mul»
                        [Var «x1»;Var «x4»];
                       App «candle_cv_fs_angle_interval_mul»
                        [Var «x2»;Var «x5»];
                       App «candle_cv_fs_interval_neg»
                        [App «candle_cv_fs_angle_interval_mul»
                          [Var «x4»;Var «x5»]];
                       App «candle_cv_fs_angle_interval_mul»
                        [Var «x0»;Var «linear»]]])))))))
End

Theorem registered_case10173_fs_hist_delta_x4_value_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_x4_value» =
    SOME
      ([«environment»],
       registered_case10173_fs_hist_delta_x4_value_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_value_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value»
        [from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_delta_x4_value_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_x4_value_lookup]
QED

Theorem registered_case10173_fs_interval_lookup_cv_list_result_eval:
  index < LENGTH values /\
  EL index values = result /\
  index + 2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [Num index;from_cv (registered_case10173_cv_list values)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> mp_tac
       (Q.SPECL [`index`,`values`,`clock`,`refs`]
          compute_registeredCase10173HistoricalCVectorEvalTheory.registered_case10173_fs_interval_lookup_cv_list_eval)
  >> simp []
QED

Theorem registered_case10173_fs_angle_six_sum_argument_results:
  registered_case10173_fs_interval_sum_object
      [r0;r1;r2;r3;r4;r5] = SOME result /\
  11 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) = (M_success (from_cv r0),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs = (M_success (from_cv r1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs = (M_success (from_cv r2),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument3 refs = (M_success (from_cv r3),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument4 refs = (M_success (from_cv r4),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument5 refs = (M_success (from_cv r5),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_six»
          [argument0;argument1;argument2;
           argument3;argument4;argument5]]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_sum»
            [from_cv
              (registered_case10173_cv_list
                [r0;r1;r2;r3;r4;r5])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_angle_six»
                [from_cv r0;from_cv r1;from_cv r2;
                 from_cv r3;from_cv r4;from_cv r5]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_interval_sum_object_list_eval
  >> simp []
QED

Theorem registered_case10173_fs_interval_neg_mul_eval:
  bounded_object_fs_interval_mul_decimal left right = SOME product /\
  bounded_object_fs_interval_neg product = SOME result /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_angle_interval_mul»
          [from_cv left;from_cv right]]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv product]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp []
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_delta_x4_value_trace_eval:
  bounded_object_fs_interval_neg x0 = SOME negative_x0 /\
  bounded_object_fs_interval_neg x3 = SOME negative_x3 /\
  registered_case10173_fs_interval_sum_object
      [negative_x0;x1;x2;negative_x3;x4;x5] = SOME linear /\
  bounded_object_fs_interval_mul_decimal x1 x2 = SOME p12 /\
  bounded_object_fs_interval_mul_decimal x0 x3 = SOME p03 /\
  bounded_object_fs_interval_mul_decimal x1 x4 = SOME p14 /\
  bounded_object_fs_interval_mul_decimal x2 x5 = SOME p25 /\
  bounded_object_fs_interval_mul_decimal x4 x5 = SOME p45 /\
  bounded_object_fs_interval_mul_decimal x0 linear = SOME p0l /\
  bounded_object_fs_interval_neg p12 = SOME negative_p12 /\
  bounded_object_fs_interval_neg p03 = SOME negative_p03 /\
  bounded_object_fs_interval_neg p45 = SOME negative_p45 /\
  registered_case10173_fs_interval_sum_object
      [negative_p12;negative_p03;p14;p25;negative_p45;p0l] =
    SOME result /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_delta_x4_value_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_x4_value_body_def,
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
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv linear`
  >> conj_tac
  >- (irule registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac
           [`negative_x0`,`x1`,`x2`,`negative_x3`,`x4`,`x5`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_angle_six_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac
       [`negative_p12`,`negative_p03`,`p14`,`p25`,`negative_p45`,`p0l`]
  >> simp
       [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
  >> rpt conj_tac
  >> irule registered_case10173_fs_interval_neg_mul_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
