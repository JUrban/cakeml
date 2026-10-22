(*****************************************************************************
 * Registered evaluator semantics for the historical six-variable delta
 * value used by the center first-order calculation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaValueEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4GradientEval
Libs
  bossLib preamble intLib

val _ = monadsyntax.temp_enable_monad "option";

Definition registered_case10173_fs_angle_delta_value_body_def:
  registered_case10173_fs_angle_delta_value_body =
    Let «x0» (App «candle_cv_fs_interval_lookup» [Num 0;Var «environment»])
      (Let «x1» (App «candle_cv_fs_interval_lookup» [Num 1;Var «environment»])
        (Let «x2» (App «candle_cv_fs_interval_lookup» [Num 2;Var «environment»])
          (Let «x3» (App «candle_cv_fs_interval_lookup» [Num 3;Var «environment»])
            (Let «x4» (App «candle_cv_fs_interval_lookup» [Num 4;Var «environment»])
              (Let «x5» (App «candle_cv_fs_interval_lookup» [Num 5;Var «environment»])
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
                      (Let «p03»
                        (App «candle_cv_fs_angle_interval_mul»
                          [Var «x0»;Var «x3»])
                        (Let «p14»
                          (App «candle_cv_fs_angle_interval_mul»
                            [Var «x1»;Var «x4»])
                          (Let «p25»
                            (App «candle_cv_fs_angle_interval_mul»
                              [Var «x2»;Var «x5»])
                            (App «candle_cv_fs_angle_interval_sum»
                              [App «candle_cv_fs_angle_seven»
                                [App «candle_cv_fs_angle_interval_mul»
                                   [Var «p03»;Var «l0»];
                                 App «candle_cv_fs_angle_interval_mul»
                                   [Var «p14»;Var «l1»];
                                 App «candle_cv_fs_angle_interval_mul»
                                   [Var «p25»;Var «l2»];
                                 App «candle_cv_fs_interval_neg»
                                   [App «candle_cv_fs_angle_interval_mul»
                                     [App «candle_cv_fs_angle_interval_mul»
                                       [Var «x1»;Var «x2»];
                                      Var «x3»]];
                                 App «candle_cv_fs_interval_neg»
                                   [App «candle_cv_fs_angle_interval_mul»
                                     [App «candle_cv_fs_angle_interval_mul»
                                       [Var «x0»;Var «x2»];
                                      Var «x4»]];
                                 App «candle_cv_fs_interval_neg»
                                   [App «candle_cv_fs_angle_interval_mul»
                                     [App «candle_cv_fs_angle_interval_mul»
                                       [Var «x0»;Var «x1»];
                                      Var «x5»]];
                                 App «candle_cv_fs_interval_neg»
                                   [App «candle_cv_fs_angle_interval_mul»
                                     [App «candle_cv_fs_angle_interval_mul»
                                       [Var «x3»;Var «x4»];
                                      Var «x5»]]]]))))))))))))
End

Theorem registered_case10173_fs_angle_delta_value_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_delta_value» =
    SOME ([«environment»],registered_case10173_fs_angle_delta_value_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_delta_value_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value» [from_cv environment])
      (refs:hol_refs) =
    compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_angle_delta_value_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_angle_delta_value_lookup]
QED

Theorem registered_case10173_compute_eval_app7_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument0 (refs:hol_refs) =
      (M_success (from_cv result0),refs) /\
  compute_eval clock ceqs argument1 refs =
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
        [argument0;argument1;argument2;argument3;
         argument4;argument5;argument6]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result0;from_cv result1;from_cv result2;from_cv result3;
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
  >> Cases_on `LENGTH q = 7`
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

Theorem registered_case10173_fs_angle_seven_sum_argument_results:
  registered_case10173_fs_interval_sum_object
      [r0;r1;r2;r3;r4;r5;r6] = SOME result /\
  12 < clock /\
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
      argument5 refs = (M_success (from_cv r5),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument6 refs = (M_success (from_cv r6),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_angle_seven»
          [argument0;argument1;argument2;argument3;
           argument4;argument5;argument6]]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_sum»
            [from_cv
              (registered_case10173_cv_list
                [r0;r1;r2;r3;r4;r5;r6])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_angle_seven»
                [from_cv r0;from_cv r1;from_cv r2;from_cv r3;
                 from_cv r4;from_cv r5;from_cv r6]) refs`
      >> conj_tac
      >- (irule registered_case10173_compute_eval_app7_argument_results
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_seven_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_interval_sum_object_list_eval
  >> simp []
QED

Theorem registered_case10173_fs_interval_neg_mul_mul_eval:
  bounded_object_fs_interval_mul_decimal left middle = SOME first_product /\
  bounded_object_fs_interval_mul_decimal first_product right =
      SOME second_product /\
  bounded_object_fs_interval_neg second_product = SOME result /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_angle_interval_mul»
          [App «candle_cv_fs_angle_interval_mul»
            [from_cv left;from_cv middle];
           from_cv right]]) (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv second_product]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp []
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_angle_interval_mul»
                [from_cv first_product;from_cv right]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> simp
               [compute_execProofTheory.compute_eval_from_cv,
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_delta_value_trace_eval:
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
  bounded_object_fs_interval_mul_decimal x0 x3 = SOME p03 /\
  bounded_object_fs_interval_mul_decimal x1 x4 = SOME p14 /\
  bounded_object_fs_interval_mul_decimal x2 x5 = SOME p25 /\
  bounded_object_fs_interval_mul_decimal p03 l0 = SOME t0 /\
  bounded_object_fs_interval_mul_decimal p14 l1 = SOME t1 /\
  bounded_object_fs_interval_mul_decimal p25 l2 = SOME t2 /\
  bounded_object_fs_interval_mul_decimal x1 x2 = SOME p12 /\
  bounded_object_fs_interval_mul_decimal p12 x3 = SOME t3 /\
  bounded_object_fs_interval_neg t3 = SOME negative_t3 /\
  bounded_object_fs_interval_mul_decimal x0 x2 = SOME p02 /\
  bounded_object_fs_interval_mul_decimal p02 x4 = SOME t4 /\
  bounded_object_fs_interval_neg t4 = SOME negative_t4 /\
  bounded_object_fs_interval_mul_decimal x0 x1 = SOME p01 /\
  bounded_object_fs_interval_mul_decimal p01 x5 = SOME t5 /\
  bounded_object_fs_interval_neg t5 = SOME negative_t5 /\
  bounded_object_fs_interval_mul_decimal x3 x4 = SOME p34 /\
  bounded_object_fs_interval_mul_decimal p34 x5 = SOME t6 /\
  bounded_object_fs_interval_neg t6 = SOME negative_t6 /\
  registered_case10173_fs_interval_sum_object
      [t0;t1;t2;negative_t3;negative_t4;negative_t5;negative_t6] =
    SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_angle_delta_value_unfold]
  >> simp
       [registered_case10173_fs_angle_delta_value_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x0`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x1`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x2`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x3`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x4`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv x5`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
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
  >> qexists_tac `from_cv p03`
  >> conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv p14`
  >> conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv p25`
  >> conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule registered_case10173_fs_angle_seven_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexistsl_tac
       [`t0`,`t1`,`t2`,`negative_t3`,`negative_t4`,`negative_t5`,`negative_t6`]
  >> simp
       [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
  >> rpt conj_tac
  >> irule registered_case10173_fs_interval_neg_mul_mul_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_angle_delta_value_object_def:
  registered_case10173_fs_angle_delta_value_object x0 x1 x2 x3 x4 x5 =
    do
      negative_x0 <- bounded_object_fs_interval_neg x0;
      negative_x3 <- bounded_object_fs_interval_neg x3;
      l0 <- registered_case10173_fs_interval_sum_object
        [negative_x0;x1;x2;negative_x3;x4;x5];
      negative_x1 <- bounded_object_fs_interval_neg x1;
      negative_x4 <- bounded_object_fs_interval_neg x4;
      l1 <- registered_case10173_fs_interval_sum_object
        [x0;negative_x1;x2;x3;negative_x4;x5];
      negative_x2 <- bounded_object_fs_interval_neg x2;
      negative_x5 <- bounded_object_fs_interval_neg x5;
      l2 <- registered_case10173_fs_interval_sum_object
        [x0;x1;negative_x2;x3;x4;negative_x5];
      p03 <- bounded_object_fs_interval_mul_decimal x0 x3;
      p14 <- bounded_object_fs_interval_mul_decimal x1 x4;
      p25 <- bounded_object_fs_interval_mul_decimal x2 x5;
      t0 <- bounded_object_fs_interval_mul_decimal p03 l0;
      t1 <- bounded_object_fs_interval_mul_decimal p14 l1;
      t2 <- bounded_object_fs_interval_mul_decimal p25 l2;
      p12 <- bounded_object_fs_interval_mul_decimal x1 x2;
      t3 <- bounded_object_fs_interval_mul_decimal p12 x3;
      negative_t3 <- bounded_object_fs_interval_neg t3;
      p02 <- bounded_object_fs_interval_mul_decimal x0 x2;
      t4 <- bounded_object_fs_interval_mul_decimal p02 x4;
      negative_t4 <- bounded_object_fs_interval_neg t4;
      p01 <- bounded_object_fs_interval_mul_decimal x0 x1;
      t5 <- bounded_object_fs_interval_mul_decimal p01 x5;
      negative_t5 <- bounded_object_fs_interval_neg t5;
      p34 <- bounded_object_fs_interval_mul_decimal x3 x4;
      t6 <- bounded_object_fs_interval_mul_decimal p34 x5;
      negative_t6 <- bounded_object_fs_interval_neg t6;
      registered_case10173_fs_interval_sum_object
        [t0;t1;t2;negative_t3;negative_t4;negative_t5;negative_t6]
    od
End

Theorem registered_case10173_fs_angle_delta_value_object_eval:
  registered_case10173_fs_angle_delta_value_object x0 x1 x2 x3 x4 x5 =
      SOME result /\
  50 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_value_object_def]
  >> every_case_tac
  >> gvs []
  >> irule registered_case10173_fs_angle_delta_value_trace_eval
  >> simp []
QED

val _ = export_theory ();
