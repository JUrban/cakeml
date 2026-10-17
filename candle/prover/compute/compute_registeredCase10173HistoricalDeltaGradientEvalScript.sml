(*****************************************************************************
 * Complete registered evaluator semantics for the historical six-variable
 * delta gradient.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaGradientEval
Ancestors
  compute_registeredCase10173HistoricalDeltaGradientComponentEval
Libs
  bossLib preamble intLib

val _ = monadsyntax.temp_enable_monad "option";

Definition registered_case10173_fs_angle_delta_gradient_body_def:
  registered_case10173_fs_angle_delta_gradient_body =
    Let «x0» (App «candle_cv_fs_interval_lookup» [Num 0;Var «environment»])
      (Let «x1» (App «candle_cv_fs_interval_lookup» [Num 1;Var «environment»])
      (Let «x2» (App «candle_cv_fs_interval_lookup» [Num 2;Var «environment»])
      (Let «x3» (App «candle_cv_fs_interval_lookup» [Num 3;Var «environment»])
      (Let «x4» (App «candle_cv_fs_interval_lookup» [Num 4;Var «environment»])
      (Let «x5» (App «candle_cv_fs_interval_lookup» [Num 5;Var «environment»])
      (Let «p00» (App «candle_cv_fs_angle_interval_mul» [Var «x0»;Var «x0»])
      (Let «p01» (App «candle_cv_fs_angle_interval_mul» [Var «x0»;Var «x1»])
      (Let «p02» (App «candle_cv_fs_angle_interval_mul» [Var «x0»;Var «x2»])
      (Let «p03» (App «candle_cv_fs_angle_interval_mul» [Var «x0»;Var «x3»])
      (Let «p04» (App «candle_cv_fs_angle_interval_mul» [Var «x0»;Var «x4»])
      (Let «p05» (App «candle_cv_fs_angle_interval_mul» [Var «x0»;Var «x5»])
      (Let «p11» (App «candle_cv_fs_angle_interval_mul» [Var «x1»;Var «x1»])
      (Let «p12» (App «candle_cv_fs_angle_interval_mul» [Var «x1»;Var «x2»])
      (Let «p13» (App «candle_cv_fs_angle_interval_mul» [Var «x1»;Var «x3»])
      (Let «p14» (App «candle_cv_fs_angle_interval_mul» [Var «x1»;Var «x4»])
      (Let «p15» (App «candle_cv_fs_angle_interval_mul» [Var «x1»;Var «x5»])
      (Let «p22» (App «candle_cv_fs_angle_interval_mul» [Var «x2»;Var «x2»])
      (Let «p23» (App «candle_cv_fs_angle_interval_mul» [Var «x2»;Var «x3»])
      (Let «p24» (App «candle_cv_fs_angle_interval_mul» [Var «x2»;Var «x4»])
      (Let «p25» (App «candle_cv_fs_angle_interval_mul» [Var «x2»;Var «x5»])
      (Let «p33» (App «candle_cv_fs_angle_interval_mul» [Var «x3»;Var «x3»])
      (Let «p34» (App «candle_cv_fs_angle_interval_mul» [Var «x3»;Var «x4»])
      (Let «p35» (App «candle_cv_fs_angle_interval_mul» [Var «x3»;Var «x5»])
      (Let «p44» (App «candle_cv_fs_angle_interval_mul» [Var «x4»;Var «x4»])
      (Let «p45» (App «candle_cv_fs_angle_interval_mul» [Var «x4»;Var «x5»])
      (Let «p55» (App «candle_cv_fs_angle_interval_mul» [Var «x5»;Var «x5»])
        (App «candle_cv_fs_angle_six»
          [App «candle_cv_fs_angle_interval_sum»
            [App «candle_cv_fs_angle_ten»
              [App «candle_cv_fs_angle_interval_scale_neg_two» [Var «p03»];
               Var «p13»;Var «p14»;
               App «candle_cv_fs_interval_neg» [Var «p15»];Var «p23»;
               App «candle_cv_fs_interval_neg» [Var «p24»];Var «p25»;
               App «candle_cv_fs_interval_neg» [Var «p33»];
               Var «p34»;Var «p35»]];
           App «candle_cv_fs_angle_interval_sum»
            [App «candle_cv_fs_angle_ten»
              [Var «p03»;Var «p04»;
               App «candle_cv_fs_interval_neg» [Var «p05»];
               App «candle_cv_fs_angle_interval_scale_neg_two» [Var «p14»];
               App «candle_cv_fs_interval_neg» [Var «p23»];
               Var «p24»;Var «p25»;Var «p34»;
               App «candle_cv_fs_interval_neg» [Var «p44»];Var «p45»]];
           App «candle_cv_fs_angle_interval_sum»
            [App «candle_cv_fs_angle_ten»
              [Var «p03»;App «candle_cv_fs_interval_neg» [Var «p04»];
               Var «p05»;App «candle_cv_fs_interval_neg» [Var «p13»];
               Var «p14»;Var «p15»;
               App «candle_cv_fs_angle_interval_scale_neg_two» [Var «p25»];
               Var «p35»;Var «p45»;
               App «candle_cv_fs_interval_neg» [Var «p55»]]];
           App «candle_cv_fs_angle_interval_sum»
            [App «candle_cv_fs_angle_ten»
              [App «candle_cv_fs_interval_neg» [Var «p00»];
               Var «p01»;Var «p02»;
               App «candle_cv_fs_angle_interval_scale_neg_two» [Var «p03»];
               Var «p04»;Var «p05»;
               App «candle_cv_fs_interval_neg» [Var «p12»];
               Var «p14»;Var «p25»;
               App «candle_cv_fs_interval_neg» [Var «p45»]]];
           App «candle_cv_fs_angle_interval_sum»
            [App «candle_cv_fs_angle_ten»
              [Var «p01»;App «candle_cv_fs_interval_neg» [Var «p02»];
               Var «p03»;App «candle_cv_fs_interval_neg» [Var «p11»];
               Var «p12»;Var «p13»;
               App «candle_cv_fs_angle_interval_scale_neg_two» [Var «p14»];
               Var «p15»;Var «p25»;
               App «candle_cv_fs_interval_neg» [Var «p35»]]];
           App «candle_cv_fs_angle_interval_sum»
            [App «candle_cv_fs_angle_ten»
              [App «candle_cv_fs_interval_neg» [Var «p01»];
               Var «p02»;Var «p03»;Var «p12»;Var «p14»;
               App «candle_cv_fs_interval_neg» [Var «p22»];
               Var «p23»;Var «p24»;
               App «candle_cv_fs_angle_interval_scale_neg_two» [Var «p25»];
               App «candle_cv_fs_interval_neg» [Var «p34»]]]
          ])))))))))))))))))))))))))))
End

Theorem registered_case10173_fs_angle_delta_gradient_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_angle_delta_gradient» =
    SOME ([«environment»],registered_case10173_fs_angle_delta_gradient_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_angle_delta_gradient_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient» [from_cv environment])
      (refs:hol_refs) =
    compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_angle_delta_gradient_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_angle_delta_gradient_lookup]
QED

fun registered_case10173_let_result_tac result =
  irule
    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac result
  >> conj_tac;

Theorem registered_case10173_fs_angle_delta_gradient_trace_eval:
  bounded_object_fs_interval_mul_decimal x0 x0 = SOME p00 /\
  bounded_object_fs_interval_mul_decimal x0 x1 = SOME p01 /\
  bounded_object_fs_interval_mul_decimal x0 x2 = SOME p02 /\
  bounded_object_fs_interval_mul_decimal x0 x3 = SOME p03 /\
  bounded_object_fs_interval_mul_decimal x0 x4 = SOME p04 /\
  bounded_object_fs_interval_mul_decimal x0 x5 = SOME p05 /\
  bounded_object_fs_interval_mul_decimal x1 x1 = SOME p11 /\
  bounded_object_fs_interval_mul_decimal x1 x2 = SOME p12 /\
  bounded_object_fs_interval_mul_decimal x1 x3 = SOME p13 /\
  bounded_object_fs_interval_mul_decimal x1 x4 = SOME p14 /\
  bounded_object_fs_interval_mul_decimal x1 x5 = SOME p15 /\
  bounded_object_fs_interval_mul_decimal x2 x2 = SOME p22 /\
  bounded_object_fs_interval_mul_decimal x2 x3 = SOME p23 /\
  bounded_object_fs_interval_mul_decimal x2 x4 = SOME p24 /\
  bounded_object_fs_interval_mul_decimal x2 x5 = SOME p25 /\
  bounded_object_fs_interval_mul_decimal x3 x3 = SOME p33 /\
  bounded_object_fs_interval_mul_decimal x3 x4 = SOME p34 /\
  bounded_object_fs_interval_mul_decimal x3 x5 = SOME p35 /\
  bounded_object_fs_interval_mul_decimal x4 x4 = SOME p44 /\
  bounded_object_fs_interval_mul_decimal x4 x5 = SOME p45 /\
  bounded_object_fs_interval_mul_decimal x5 x5 = SOME p55 /\
  registered_case10173_fs_angle_delta_gradient_component0_object
      p03 p13 p14 p15 p23 p24 p25 p33 p34 p35 = SOME g0 /\
  registered_case10173_fs_angle_delta_gradient_component1_object
      p03 p04 p05 p14 p23 p24 p25 p34 p44 p45 = SOME g1 /\
  registered_case10173_fs_angle_delta_gradient_component2_object
      p03 p04 p05 p13 p14 p15 p25 p35 p45 p55 = SOME g2 /\
  registered_case10173_fs_angle_delta_gradient_component3_object
      p00 p01 p02 p03 p04 p05 p12 p14 p25 p45 = SOME g3 /\
  registered_case10173_fs_angle_delta_gradient_component4_object
      p01 p02 p03 p11 p12 p13 p14 p15 p25 p35 = SOME g4 /\
  registered_case10173_fs_angle_delta_gradient_component5_object
      p01 p02 p03 p12 p14 p22 p23 p24 p25 p34 = SOME g5 /\
  90 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_list [g0;g1;g2;g3;g4;g5])),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_angle_delta_gradient_unfold]
  >> simp
       [registered_case10173_fs_angle_delta_gradient_body_def,
        compute_evalTheory.subst_def]
  >> registered_case10173_let_result_tac `from_cv x0`
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv x1`
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv x2`
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv x3`
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv x4`
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv x5`
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp [] >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p00`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p01`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p02`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p03`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p04`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p05`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p11`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p12`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p13`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p14`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p15`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p22`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p23`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p24`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p25`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p33`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p34`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p35`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p44`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p45`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> registered_case10173_let_result_tac `from_cv p55`
  >- (simp [compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval]
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 28) registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv g0;from_cv g1;from_cv g2;
             from_cv g3;from_cv g4;from_cv g5]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp
           [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component0_object_eval,
            compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component1_object_eval,
            compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component2_object_eval,
            compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component3_object_eval,
            compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component4_object_eval,
            compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component5_object_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_angle_delta_gradient_object_def:
  registered_case10173_fs_angle_delta_gradient_object x0 x1 x2 x3 x4 x5 =
    do
      p00 <- bounded_object_fs_interval_mul_decimal x0 x0;
      p01 <- bounded_object_fs_interval_mul_decimal x0 x1;
      p02 <- bounded_object_fs_interval_mul_decimal x0 x2;
      p03 <- bounded_object_fs_interval_mul_decimal x0 x3;
      p04 <- bounded_object_fs_interval_mul_decimal x0 x4;
      p05 <- bounded_object_fs_interval_mul_decimal x0 x5;
      p11 <- bounded_object_fs_interval_mul_decimal x1 x1;
      p12 <- bounded_object_fs_interval_mul_decimal x1 x2;
      p13 <- bounded_object_fs_interval_mul_decimal x1 x3;
      p14 <- bounded_object_fs_interval_mul_decimal x1 x4;
      p15 <- bounded_object_fs_interval_mul_decimal x1 x5;
      p22 <- bounded_object_fs_interval_mul_decimal x2 x2;
      p23 <- bounded_object_fs_interval_mul_decimal x2 x3;
      p24 <- bounded_object_fs_interval_mul_decimal x2 x4;
      p25 <- bounded_object_fs_interval_mul_decimal x2 x5;
      p33 <- bounded_object_fs_interval_mul_decimal x3 x3;
      p34 <- bounded_object_fs_interval_mul_decimal x3 x4;
      p35 <- bounded_object_fs_interval_mul_decimal x3 x5;
      p44 <- bounded_object_fs_interval_mul_decimal x4 x4;
      p45 <- bounded_object_fs_interval_mul_decimal x4 x5;
      p55 <- bounded_object_fs_interval_mul_decimal x5 x5;
      g0 <- registered_case10173_fs_angle_delta_gradient_component0_object
        p03 p13 p14 p15 p23 p24 p25 p33 p34 p35;
      g1 <- registered_case10173_fs_angle_delta_gradient_component1_object
        p03 p04 p05 p14 p23 p24 p25 p34 p44 p45;
      g2 <- registered_case10173_fs_angle_delta_gradient_component2_object
        p03 p04 p05 p13 p14 p15 p25 p35 p45 p55;
      g3 <- registered_case10173_fs_angle_delta_gradient_component3_object
        p00 p01 p02 p03 p04 p05 p12 p14 p25 p45;
      g4 <- registered_case10173_fs_angle_delta_gradient_component4_object
        p01 p02 p03 p11 p12 p13 p14 p15 p25 p35;
      g5 <- registered_case10173_fs_angle_delta_gradient_component5_object
        p01 p02 p03 p12 p14 p22 p23 p24 p25 p34;
      return (registered_case10173_cv_list [g0;g1;g2;g3;g4;g5])
    od
End

Theorem registered_case10173_fs_angle_delta_gradient_object_eval:
  registered_case10173_fs_angle_delta_gradient_object x0 x1 x2 x3 x4 x5 =
      SOME result /\
  90 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> fs [registered_case10173_fs_angle_delta_gradient_object_def]
  >> every_case_tac >> gvs []
  >> irule registered_case10173_fs_angle_delta_gradient_trace_eval
  >> simp []
QED

val _ = export_theory ();
