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

val _ = export_theory ();
