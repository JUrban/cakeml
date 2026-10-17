(*****************************************************************************
 * Registered evaluator semantics for the gradient prefix of the historical
 * three-variable u calculation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUThreeGradientEval
Ancestors
  compute_registeredCase10173HistoricalUEmbeddingEval
  compute_registeredCase10173HistoricalAtanConstantEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u_three_after_gradients_body_def:
  registered_case10173_fs_hist_u_three_after_gradients_body =
    Let «points0»
      (App «candle_cv_fs_hist_u_points» [Var «x0»;Var «g0»])
      (Let «points1»
        (App «candle_cv_fs_hist_u_points» [Var «x1»;Var «g1»])
        (Let «points2»
          (App «candle_cv_fs_hist_u_points» [Var «x2»;Var «g2»])
          (Let «lower»
            (App «candle_cv_fs_hist_u_value_formula»
              [Num 2;Var «points0»;Var «points1»;Var «points2»])
            (Let «upper»
              (App «candle_cv_fs_hist_u_value_formula»
                [Num 0;Var «points0»;Var «points1»;Var «points2»])
              (Pair
                (Pair (Uop Fst (Var «lower»))
                  (Uop Snd (Var «upper»)))
                (App «candle_cv_fs_hist_three»
                  [Var «g0»;Var «g1»;Var «g2»]))))))
End

Definition registered_case10173_fs_hist_u_three_body_def:
  registered_case10173_fs_hist_u_three_body =
    Let «g0»
      (App «candle_cv_fs_angle_interval_scale»
        [Num 2;
         App «candle_cv_fs_angle_interval_sum»
           [App «candle_cv_fs_hist_three»
             [App «candle_cv_fs_interval_neg» [Var «x0»];
              Var «x1»;Var «x2»]]])
      (Let «g1»
        (App «candle_cv_fs_angle_interval_scale»
          [Num 2;
           App «candle_cv_fs_angle_interval_sum»
             [App «candle_cv_fs_hist_three»
               [Var «x0»;
                App «candle_cv_fs_interval_neg» [Var «x1»];
                Var «x2»]]])
        (Let «g2»
          (App «candle_cv_fs_angle_interval_scale»
            [Num 2;
             App «candle_cv_fs_angle_interval_sum»
               [App «candle_cv_fs_hist_three»
                 [Var «x0»;Var «x1»;
                  App «candle_cv_fs_interval_neg» [Var «x2»]]]])
          registered_case10173_fs_hist_u_three_after_gradients_body))
End

Theorem registered_case10173_fs_hist_u_three_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_u_three» =
    SOME
      ([«x0»;«x1»;«x2»],
       registered_case10173_fs_hist_u_three_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_u_three_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [from_cv x0;from_cv x1;from_cv x2]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2)]
        registered_case10173_fs_hist_u_three_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_hist_compute_eval_literal_app3
  >> simp [registered_case10173_fs_hist_u_three_lookup]
QED

Theorem registered_case10173_fs_hist_scaled_three_sum_argument_results:
  registered_case10173_fs_interval_sum_object [r0;r1;r2] = SOME half /\
  registered_case10173_fs_interval_raw_scale_object 2 half = SOME result /\
  12 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) = (M_success (from_cv r0),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs = (M_success (from_cv r1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs = (M_success (from_cv r2),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [Num 2;
         App «candle_cv_fs_angle_interval_sum»
           [App «candle_cv_fs_hist_three»
             [argument0;argument1;argument2]]]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_scale»
            [from_cv (Num 2);from_cv half]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (mp_tac
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`x` |-> `(Num 2:cv)`, `s` |-> `refs`,
                `ck` |-> `clock`,
                `eqs` |->
                  `registered_case10173_historical_chunk16_ceqs`]
               (SPEC_ALL compute_execProofTheory.compute_eval_from_cv)))
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_hist_three_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`r0`,`r1`,`r2`]
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u_three_gradient_prefix_eval:
  bounded_object_fs_interval_neg x0 = SOME negative_x0 /\
  registered_case10173_fs_interval_sum_object
      [negative_x0;x1;x2] = SOME g0_half /\
  registered_case10173_fs_interval_raw_scale_object 2 g0_half = SOME g0 /\
  bounded_object_fs_interval_neg x1 = SOME negative_x1 /\
  registered_case10173_fs_interval_sum_object
      [x0;negative_x1;x2] = SOME g1_half /\
  registered_case10173_fs_interval_raw_scale_object 2 g1_half = SOME g1 /\
  bounded_object_fs_interval_neg x2 = SOME negative_x2 /\
  registered_case10173_fs_interval_sum_object
      [x0;x1;negative_x2] = SOME g2_half /\
  registered_case10173_fs_interval_raw_scale_object 2 g2_half = SOME g2 /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [from_cv x0;from_cv x1;from_cv x2]) (refs:hol_refs) =
    compute_eval (clock - 4)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
         («g0»,from_cv g0);(«g1»,from_cv g1);(«g2»,from_cv g2)]
        registered_case10173_fs_hist_u_three_after_gradients_body) refs
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_u_three_unfold]
  >> simp
       [registered_case10173_fs_hist_u_three_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv g0`
  >> conj_tac
  >- (irule registered_case10173_fs_hist_scaled_three_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`g0_half`,`negative_x0`,`x1`,`x2`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv g1`
  >> conj_tac
  >- (irule registered_case10173_fs_hist_scaled_three_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`g1_half`,`x0`,`negative_x1`,`x2`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv g2`
  >> conj_tac
  >- (irule registered_case10173_fs_hist_scaled_three_sum_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexistsl_tac [`g2_half`,`x0`,`x1`,`negative_x2`]
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval]
      >> intLib.ARITH_TAC)
  >> simp
       [registered_case10173_fs_hist_u_three_after_gradients_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
QED

val _ = export_theory ();
