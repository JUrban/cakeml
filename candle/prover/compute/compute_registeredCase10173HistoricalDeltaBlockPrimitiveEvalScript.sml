(*****************************************************************************
 * Registered evaluator semantics for the raw primitives shared by the
 * historical delta gradient and value blocks.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaBlockPrimitiveEval
Ancestors
  compute_registeredCase10173HistoricalDeltaHessianEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_round_scale_body_def:
  registered_case10173_fs_hist_round_scale_body =
    App «candle_cv_fs_raw_interval_round»
      [App «candle_cv_fs_scale» [];Var «raw»]
End

Theorem registered_case10173_fs_hist_round_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_round_scale» =
    SOME ([«raw»],registered_case10173_fs_hist_round_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_round_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_round_scale» [from_cv raw])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«raw»,from_cv raw)]
        registered_case10173_fs_hist_round_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_round_scale_lookup]
QED

Theorem registered_case10173_fs_hist_round_scale_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw = SOME result /\
  12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_round_scale» [from_cv raw])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_round_scale_unfold]
  >> simp
       [registered_case10173_fs_hist_round_scale_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173HistoricalUValueEvalTheory.registered_case10173_fs_round_scale_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_hist_raw_cubic_body_def:
  registered_case10173_fs_hist_raw_cubic_body =
    App «candle_cv_fs_raw_interval_mul»
      [App «candle_cv_fs_raw_interval_mul» [Var «first»;Var «second»];
       Var «third»]
End

Theorem registered_case10173_fs_hist_raw_cubic_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_raw_cubic» =
    SOME
      ([«first»;«second»;«third»],
       registered_case10173_fs_hist_raw_cubic_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_raw_cubic_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_raw_cubic»
        [from_cv first_value;from_cv second_value;from_cv third_value])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«first»,from_cv first_value);(«second»,from_cv second_value);
         («third»,from_cv third_value)]
        registered_case10173_fs_hist_raw_cubic_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_raw_cubic_lookup]
QED

Theorem registered_case10173_fs_hist_raw_cubic_eval:
  bounded_object_fs_raw_interval_mul first_value second_value = SOME product /\
  bounded_object_fs_raw_interval_mul product third_value = SOME result /\
  6 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_raw_cubic»
        [from_cv first_value;from_cv second_value;from_cv third_value])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_raw_cubic_unfold]
  >> simp
       [registered_case10173_fs_hist_raw_cubic_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_mul»
            [from_cv product;from_cv third_value]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalUValueEvalTheory.registered_case10173_fs_raw_interval_mul_result_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalUValueEvalTheory.registered_case10173_fs_raw_interval_mul_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_interval_neg_hist_raw_cubic_eval:
  bounded_object_fs_raw_interval_mul first_value second_value = SOME product /\
  bounded_object_fs_raw_interval_mul product third_value = SOME cubic /\
  bounded_object_fs_interval_neg cubic = SOME result /\
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_hist_raw_cubic»
          [from_cv first_value;from_cv second_value;from_cv third_value]])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv cubic]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp [registered_case10173_fs_hist_raw_cubic_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Theorem registered_case10173_fs_round_scale_squared_result_eval:
  bounded_object_fs_raw_interval_round 1000000000000000000000000 raw =
      SOME result /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_round»
        [App «candle_cv_fs_scale_squared» [];from_cv raw])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_round»
            [from_cv (Num 1000000000000000000000000);from_cv raw]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_squared_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval
  >> simp []
QED

Definition registered_case10173_fs_hist_delta_value_block_body_def:
  registered_case10173_fs_hist_delta_value_block_body =
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
    (Let «l0»
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_six»
          [App «candle_cv_fs_interval_neg» [Var «x0»];
           Var «x1»;Var «x2»;
           App «candle_cv_fs_interval_neg» [Var «x3»];
           Var «x4»;Var «x5»]])
    (Let «l1»
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_six»
          [Var «x0»;
           App «candle_cv_fs_interval_neg» [Var «x1»];
           Var «x2»;Var «x3»;
           App «candle_cv_fs_interval_neg» [Var «x4»];
           Var «x5»]])
    (Let «l2»
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_six»
          [Var «x0»;Var «x1»;
           App «candle_cv_fs_interval_neg» [Var «x2»];
           Var «x3»;Var «x4»;
           App «candle_cv_fs_interval_neg» [Var «x5»]]])
    (Let «raw»
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_seven»
          [App «candle_cv_fs_hist_raw_cubic» [Var «x0»;Var «x3»;Var «l0»];
           App «candle_cv_fs_hist_raw_cubic» [Var «x1»;Var «x4»;Var «l1»];
           App «candle_cv_fs_hist_raw_cubic» [Var «x2»;Var «x5»;Var «l2»];
           App «candle_cv_fs_interval_neg»
             [App «candle_cv_fs_hist_raw_cubic»
               [Var «x1»;Var «x2»;Var «x3»]];
           App «candle_cv_fs_interval_neg»
             [App «candle_cv_fs_hist_raw_cubic»
               [Var «x0»;Var «x2»;Var «x4»]];
           App «candle_cv_fs_interval_neg»
             [App «candle_cv_fs_hist_raw_cubic»
               [Var «x0»;Var «x1»;Var «x5»]];
           App «candle_cv_fs_interval_neg»
             [App «candle_cv_fs_hist_raw_cubic»
               [Var «x3»;Var «x4»;Var «x5»]]]])
      (App «candle_cv_fs_raw_interval_round»
        [App «candle_cv_fs_scale_squared» [];Var «raw»]))))))))))
End

Theorem registered_case10173_fs_hist_delta_value_block_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_value_block» =
    SOME
      ([«environment»],registered_case10173_fs_hist_delta_value_block_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_value_block_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_value_block» [from_cv environment])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_delta_value_block_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_value_block_lookup]
QED

Theorem registered_case10173_fs_hist_delta_value_block_trace_eval:
  bounded_object_fs_interval_neg x0 = SOME negative_x0 /\
  bounded_object_fs_interval_neg x3 = SOME negative_x3 /\
  registered_case10173_fs_interval_sum_object
      [negative_x0;x1;x2;negative_x3;x4;x5] = SOME l0 /\
  bounded_object_fs_interval_neg x1 = SOME negative_x1 /\
  bounded_object_fs_interval_neg x4 = SOME negative_x4 /\
  registered_case10173_fs_interval_sum_object
      [x0;negative_x1;x2;x3;negative_x4;x5] = SOME l1 /\
  bounded_object_fs_interval_neg x2 = SOME negative_x2 /\
  bounded_object_fs_interval_neg x5 = SOME negative_x5 /\
  registered_case10173_fs_interval_sum_object
      [x0;x1;negative_x2;x3;x4;negative_x5] = SOME l2 /\
  bounded_object_fs_raw_interval_mul x0 x3 = SOME p03 /\
  bounded_object_fs_raw_interval_mul p03 l0 = SOME t0 /\
  bounded_object_fs_raw_interval_mul x1 x4 = SOME p14 /\
  bounded_object_fs_raw_interval_mul p14 l1 = SOME t1 /\
  bounded_object_fs_raw_interval_mul x2 x5 = SOME p25 /\
  bounded_object_fs_raw_interval_mul p25 l2 = SOME t2 /\
  bounded_object_fs_raw_interval_mul x1 x2 = SOME p12 /\
  bounded_object_fs_raw_interval_mul p12 x3 = SOME t3 /\
  bounded_object_fs_interval_neg t3 = SOME negative_t3 /\
  bounded_object_fs_raw_interval_mul x0 x2 = SOME p02 /\
  bounded_object_fs_raw_interval_mul p02 x4 = SOME t4 /\
  bounded_object_fs_interval_neg t4 = SOME negative_t4 /\
  bounded_object_fs_raw_interval_mul x0 x1 = SOME p01 /\
  bounded_object_fs_raw_interval_mul p01 x5 = SOME t5 /\
  bounded_object_fs_interval_neg t5 = SOME negative_t5 /\
  bounded_object_fs_raw_interval_mul x3 x4 = SOME p34 /\
  bounded_object_fs_raw_interval_mul p34 x5 = SOME t6 /\
  bounded_object_fs_interval_neg t6 = SOME negative_t6 /\
  registered_case10173_fs_interval_sum_object
      [t0;t1;t2;negative_t3;negative_t4;negative_t5;negative_t6] =
    SOME raw /\
  bounded_object_fs_raw_interval_round 1000000000000000000000000 raw =
    SOME result /\
  60 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_value_block»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_delta_value_block_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_value_block_body_def,
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
  >> qexists_tac `from_cv l0`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`negative_x0`,`x1`,`x2`,`negative_x3`,`x4`,`x5`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv l1`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`x0`,`negative_x1`,`x2`,`x3`,`negative_x4`,`x5`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv l2`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_angle_six_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`x0`,`x1`,`negative_x2`,`x3`,`x4`,`negative_x5`]
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
        compute_registeredCase10173HistoricalDeltaValueEvalTheory.registered_case10173_fs_angle_seven_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac
           [`t0`,`t1`,`t2`,`negative_t3`,`negative_t4`,`negative_t5`,
            `negative_t6`]
      >> simp
           [registered_case10173_fs_hist_raw_cubic_eval,
            registered_case10173_fs_interval_neg_hist_raw_cubic_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_round_scale_squared_result_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
