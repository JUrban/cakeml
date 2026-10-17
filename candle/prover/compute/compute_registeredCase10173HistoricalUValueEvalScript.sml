(*****************************************************************************
 * Registered evaluator semantics for the historical u value formula.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUValueEval
Ancestors
  compute_registeredCase10173HistoricalUPointsEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u_value_formula_body_def:
  registered_case10173_fs_hist_u_value_formula_body =
    Let «n0»
      (App «candle_cv_fs_interval_lookup»
        [Var «selector»;Var «points0»])
      (Let «n1»
        (App «candle_cv_fs_interval_lookup»
          [Var «selector»;Var «points1»])
        (Let «n2»
          (App «candle_cv_fs_interval_lookup»
            [Var «selector»;Var «points2»])
          (Let «positive_selector»
            (Binop Add (Var «selector») (Num 1))
            (Let «p0»
              (App «candle_cv_fs_interval_lookup»
                [Var «positive_selector»;Var «points0»])
              (Let «p1»
                (App «candle_cv_fs_interval_lookup»
                  [Var «positive_selector»;Var «points1»])
                (Let «p2»
                  (App «candle_cv_fs_interval_lookup»
                    [Var «positive_selector»;Var «points2»])
                  (Let «raw»
                    (App «candle_cv_fs_angle_interval_sum»
                      [App «candle_cv_fs_angle_six»
                        [App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_raw_interval_mul»
                            [Var «n0»;Var «n0»]];
                         App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_raw_interval_mul»
                            [Var «n1»;Var «n1»]];
                         App «candle_cv_fs_interval_neg»
                          [App «candle_cv_fs_raw_interval_mul»
                            [Var «n2»;Var «n2»]];
                         App «candle_cv_fs_angle_interval_scale»
                          [Num 2;
                           App «candle_cv_fs_raw_interval_mul»
                            [Var «p0»;Var «p1»]];
                         App «candle_cv_fs_angle_interval_scale»
                          [Num 2;
                           App «candle_cv_fs_raw_interval_mul»
                            [Var «p1»;Var «p2»]];
                         App «candle_cv_fs_angle_interval_scale»
                          [Num 2;
                           App «candle_cv_fs_raw_interval_mul»
                            [Var «p2»;Var «p0»]]]])
                    (App «candle_cv_fs_raw_interval_round»
                      [App «candle_cv_fs_scale» [];Var «raw»]))))))))
End

Theorem registered_case10173_fs_hist_u_value_formula_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_u_value_formula» =
    SOME
      ([«selector»;«points0»;«points1»;«points2»],
       registered_case10173_fs_hist_u_value_formula_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_u_value_formula_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_value_formula»
        [from_cv selector;from_cv points0;from_cv points1;from_cv points2])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«selector»,from_cv selector);(«points0»,from_cv points0);
         («points1»,from_cv points1);(«points2»,from_cv points2)]
        registered_case10173_fs_hist_u_value_formula_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_hist_u_value_formula_lookup]
QED

Theorem registered_case10173_compute_eval_binop_add_num:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Binop Add (Num left) (Num right)) (refs:hol_refs) =
    (M_success (from_cv (Num (left + right))),refs)
Proof
  Cases_on `clock`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_arith_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_raw_interval_mul_result_eval:
  bounded_object_fs_raw_interval_mul left right = SOME result /\
  2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_mul» [from_cv left;from_cv right])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> Cases_on `result`
  >- (Cases_on `left`
      >> Cases_on `right`
      >> fs
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def]
      >> every_case_tac
      >> fs
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_extrema_def]
      >> every_case_tac
      >> gvs [])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_raw_interval_mul_eval
  >> simp []
QED

Theorem registered_case10173_fs_interval_neg_raw_mul_eval:
  bounded_object_fs_raw_interval_mul left right = SOME product /\
  bounded_object_fs_interval_neg product = SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_raw_interval_mul»
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
      >> simp [registered_case10173_fs_raw_interval_mul_result_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Theorem registered_case10173_fs_scale_raw_mul_eval:
  bounded_object_fs_raw_interval_mul left right = SOME product /\
  registered_case10173_fs_interval_raw_scale_object factor product =
      SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [from_cv (Num factor);
         App «candle_cv_fs_raw_interval_mul»
          [from_cv left;from_cv right]]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_scale»
            [from_cv (Num factor);from_cv product]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            registered_case10173_fs_raw_interval_mul_result_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_round_scale_result_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw = SOME result /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_round»
        [App «candle_cv_fs_scale» [];from_cv raw]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_round»
            [from_cv (Num 1000000000000);from_cv raw]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_u_value_formula_trace_eval:
  selector < LENGTH points0 /\ EL selector points0 = n0 /\
  selector < LENGTH points1 /\ EL selector points1 = n1 /\
  selector < LENGTH points2 /\ EL selector points2 = n2 /\
  selector + 1 < LENGTH points0 /\ EL (selector + 1) points0 = p0 /\
  selector + 1 < LENGTH points1 /\ EL (selector + 1) points1 = p1 /\
  selector + 1 < LENGTH points2 /\ EL (selector + 1) points2 = p2 /\
  bounded_object_fs_raw_interval_mul n0 n0 = SOME n0_square /\
  bounded_object_fs_interval_neg n0_square = SOME negative_n0_square /\
  bounded_object_fs_raw_interval_mul n1 n1 = SOME n1_square /\
  bounded_object_fs_interval_neg n1_square = SOME negative_n1_square /\
  bounded_object_fs_raw_interval_mul n2 n2 = SOME n2_square /\
  bounded_object_fs_interval_neg n2_square = SOME negative_n2_square /\
  bounded_object_fs_raw_interval_mul p0 p1 = SOME p01 /\
  registered_case10173_fs_interval_raw_scale_object 2 p01 = SOME twice_p01 /\
  bounded_object_fs_raw_interval_mul p1 p2 = SOME p12 /\
  registered_case10173_fs_interval_raw_scale_object 2 p12 = SOME twice_p12 /\
  bounded_object_fs_raw_interval_mul p2 p0 = SOME p20 /\
  registered_case10173_fs_interval_raw_scale_object 2 p20 = SOME twice_p20 /\
  registered_case10173_fs_interval_sum_object
      [negative_n0_square;negative_n1_square;negative_n2_square;
       twice_p01;twice_p12;twice_p20] = SOME raw /\
  bounded_object_fs_raw_interval_round 1000000000000 raw = SOME result /\
  selector + 40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_value_formula»
        [from_cv (Num selector);
         from_cv (registered_case10173_cv_list points0);
         from_cv (registered_case10173_cv_list points1);
         from_cv (registered_case10173_cv_list points2)]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_u_value_formula_unfold]
  >> simp
       [registered_case10173_fs_hist_u_value_formula_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv n0`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv n1`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv n2`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (Num (selector + 1))`
  >> conj_tac
  >- (irule registered_case10173_compute_eval_binop_add_num
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv p0`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv p1`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv p2`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
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
           [`negative_n0_square`,`negative_n1_square`,`negative_n2_square`,
            `twice_p01`,`twice_p12`,`twice_p20`]
      >> simp [registered_case10173_fs_interval_neg_raw_mul_eval]
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              registered_case10173_fs_scale_raw_mul_eval)
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac `p01`
          >> simp [])
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              registered_case10173_fs_scale_raw_mul_eval)
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac `p12`
          >> simp [])
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_scale_raw_mul_eval)
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `p20`
      >> simp [])
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_round_scale_result_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> metis_tac []
QED

val _ = export_theory ();
