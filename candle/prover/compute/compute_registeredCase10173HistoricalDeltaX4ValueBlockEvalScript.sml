(*****************************************************************************
 * Registered evaluator semantics for the historical delta_x4 box value.
 *
 * Unlike the center-value source, this block preserves raw products until a
 * single outward rounding step.  The trace theorem follows that source order
 * exactly, so the later typed refinement need not assume reassociation of
 * bounded interval operations.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4ValueBlockEval
Ancestors
  compute_registeredCase10173HistoricalMonotoneEval
  compute_registeredCase10173HistoricalUValueEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_raw_product_body_def:
  registered_case10173_fs_hist_raw_product_body =
    App «candle_cv_fs_raw_interval_mul» [Var «left»;Var «right»]
End

Theorem registered_case10173_fs_hist_raw_product_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_raw_product» =
    SOME
      ([«left»;«right»],
       registered_case10173_fs_hist_raw_product_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_raw_product_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_raw_product»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«left»,from_cv left);(«right»,from_cv right)]
        registered_case10173_fs_hist_raw_product_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_hist_raw_product_lookup]
QED

Theorem registered_case10173_fs_hist_raw_product_eval:
  bounded_object_fs_raw_interval_mul left right = SOME result /\
  3 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_raw_product»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_raw_product_unfold]
  >> simp
       [registered_case10173_fs_hist_raw_product_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_raw_interval_mul_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_interval_neg_hist_raw_product_eval:
  bounded_object_fs_raw_interval_mul left right = SOME product /\
  bounded_object_fs_interval_neg product = SOME result /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_hist_raw_product»
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
      >> simp [registered_case10173_fs_hist_raw_product_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Definition registered_case10173_fs_hist_delta_x4_value_block_body_def:
  registered_case10173_fs_hist_delta_x4_value_block_body =
    Let «x0»
      (App «candle_cv_fs_interval_lookup» [Num 0;Var «environment»])
      (Let «x1»
        (App «candle_cv_fs_interval_lookup» [Num 1;Var «environment»])
        (Let «x2»
          (App «candle_cv_fs_interval_lookup» [Num 2;Var «environment»])
          (Let «x3»
            (App «candle_cv_fs_interval_lookup» [Num 3;Var «environment»])
            (Let «x4»
              (App «candle_cv_fs_interval_lookup» [Num 4;Var «environment»])
              (Let «x5»
                (App «candle_cv_fs_interval_lookup» [Num 5;Var «environment»])
                (Let «linear»
                  (App «candle_cv_fs_angle_interval_sum»
                    [App «candle_cv_fs_angle_six»
                      [App «candle_cv_fs_interval_neg» [Var «x0»];
                       Var «x1»;Var «x2»;
                       App «candle_cv_fs_interval_neg» [Var «x3»];
                       Var «x4»;Var «x5»]])
                  (Let «raw»
                    (App «candle_cv_fs_angle_interval_sum»
                      [App «candle_cv_fs_angle_six»
                        [App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_hist_raw_product»
                            [Var «x1»;Var «x2»]];
                         App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_hist_raw_product»
                            [Var «x0»;Var «x3»]];
                         App «candle_cv_fs_hist_raw_product»
                          [Var «x1»;Var «x4»];
                         App «candle_cv_fs_hist_raw_product»
                          [Var «x2»;Var «x5»];
                         App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_hist_raw_product»
                            [Var «x4»;Var «x5»]];
                         App «candle_cv_fs_hist_raw_product»
                          [Var «x0»;Var «linear»]]])
                    (App «candle_cv_fs_raw_interval_round»
                      [App «candle_cv_fs_scale» [];Var «raw»]))))))))
End

Theorem registered_case10173_fs_hist_delta_x4_value_block_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_x4_value_block» =
    SOME
      ([«environment»],
       registered_case10173_fs_hist_delta_x4_value_block_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_value_block_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value_block»
        [from_cv environment]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_delta_x4_value_block_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_x4_value_block_lookup]
QED

Theorem registered_case10173_fs_hist_delta_x4_value_block_trace_eval:
  bounded_object_fs_interval_neg x0 = SOME negative_x0 /\
  bounded_object_fs_interval_neg x3 = SOME negative_x3 /\
  registered_case10173_fs_interval_sum_object
      [negative_x0;x1;x2;negative_x3;x4;x5] = SOME linear /\
  bounded_object_fs_raw_interval_mul x1 x2 = SOME p12 /\
  bounded_object_fs_interval_neg p12 = SOME negative_p12 /\
  bounded_object_fs_raw_interval_mul x0 x3 = SOME p03 /\
  bounded_object_fs_interval_neg p03 = SOME negative_p03 /\
  bounded_object_fs_raw_interval_mul x1 x4 = SOME p14 /\
  bounded_object_fs_raw_interval_mul x2 x5 = SOME p25 /\
  bounded_object_fs_raw_interval_mul x4 x5 = SOME p45 /\
  bounded_object_fs_interval_neg p45 = SOME negative_p45 /\
  bounded_object_fs_raw_interval_mul x0 linear = SOME p0l /\
  registered_case10173_fs_interval_sum_object
      [negative_p12;negative_p03;p14;p25;negative_p45;p0l] =
    SOME raw /\
  bounded_object_fs_raw_interval_round 1000000000000 raw = SOME result /\
  29 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value_block»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_delta_x4_value_block_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_x4_value_block_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x0`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x1`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x2`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x3`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x4`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x5`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv linear`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac
           [`negative_x0`,`x1`,`x2`,`negative_x3`,`x4`,`x5`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv raw`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac
           [`negative_p12`,`negative_p03`,`p14`,`p25`,`negative_p45`,`p0l`]
      >> simp [registered_case10173_fs_interval_neg_hist_raw_product_eval]
      >> rpt conj_tac
      >> irule registered_case10173_fs_hist_raw_product_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_round_scale_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
