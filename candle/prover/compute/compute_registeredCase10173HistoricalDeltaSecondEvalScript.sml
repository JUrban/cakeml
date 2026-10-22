(*****************************************************************************
 * Registered-source refinement for the complete historical delta jet.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaSecondEval
Ancestors
  compute_registeredCase10173HistoricalDeltaGradientBoxEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_hist_delta_gradient_six_typed_eval:
  LENGTH environment = 6 /\
  LENGTH r0 = 6 /\ LENGTH r1 = 6 /\ LENGTH r2 = 6 /\
  LENGTH r3 = 6 /\ LENGTH r4 = 6 /\ LENGTH r5 = 6 /\
  bounded_historical_delta_gradient_box_decimal
      environment [0;1;2;3;4;5] [r0;r1;r2;r3;r4;r5] = SOME gradient /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_hist_delta_gradient_sign_entry»
           [Num 0;from_cv (bounded_interval64_object_cv_list environment);
            from_cv
              (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])];
         App «candle_cv_fs_hist_delta_gradient_sign_entry»
           [Num 1;from_cv (bounded_interval64_object_cv_list environment);
            from_cv
              (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])];
         App «candle_cv_fs_hist_delta_gradient_sign_entry»
           [Num 2;from_cv (bounded_interval64_object_cv_list environment);
            from_cv
              (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])];
         App «candle_cv_fs_hist_delta_gradient_sign_entry»
           [Num 3;from_cv (bounded_interval64_object_cv_list environment);
            from_cv
              (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])];
         App «candle_cv_fs_hist_delta_gradient_sign_entry»
           [Num 4;from_cv (bounded_interval64_object_cv_list environment);
            from_cv
              (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])];
         App «candle_cv_fs_hist_delta_gradient_sign_entry»
           [Num 5;from_cv (bounded_interval64_object_cv_list environment);
            from_cv
              (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list gradient)),refs)
Proof
  rpt strip_tac
  >> Cases_on
       `bounded_historical_delta_gradient_box_entry_decimal environment r0 0`
  >> Cases_on
       `bounded_historical_delta_gradient_box_entry_decimal environment r1 1`
  >> Cases_on
       `bounded_historical_delta_gradient_box_entry_decimal environment r2 2`
  >> Cases_on
       `bounded_historical_delta_gradient_box_entry_decimal environment r3 3`
  >> Cases_on
       `bounded_historical_delta_gradient_box_entry_decimal environment r4 4`
  >> Cases_on
       `bounded_historical_delta_gradient_box_entry_decimal environment r5 5`
  >> gvs
       [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_box_decimal_def]
  >> rename1
       `bounded_historical_delta_gradient_box_entry_decimal environment r0 0 =
        SOME g0`
  >> rename1
       `bounded_historical_delta_gradient_box_entry_decimal environment r1 1 =
        SOME g1`
  >> rename1
       `bounded_historical_delta_gradient_box_entry_decimal environment r2 2 =
        SOME g2`
  >> rename1
       `bounded_historical_delta_gradient_box_entry_decimal environment r3 3 =
        SOME g3`
  >> rename1
       `bounded_historical_delta_gradient_box_entry_decimal environment r4 4 =
        SOME g4`
  >> rename1
       `bounded_historical_delta_gradient_box_entry_decimal environment r5 5 =
        SOME g5`
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv (bounded_interval64_object_cv g0);
             from_cv (bounded_interval64_object_cv g1);
             from_cv (bounded_interval64_object_cv g2);
             from_cv (bounded_interval64_object_cv g3);
             from_cv (bounded_interval64_object_cv g4);
             from_cv (bounded_interval64_object_cv g5)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_delta_gradient_sign_entry_typed_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> rw
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval)
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_hist_delta_second_body_def:
  registered_case10173_fs_hist_delta_second_body =
    Let «hessian»
      (App «candle_cv_fs_angle_delta_hessian» [Var «boxes»])
      (Let «gradient»
        (App «candle_cv_fs_angle_six»
          [App «candle_cv_fs_hist_delta_gradient_sign_entry»
             [Num 0;Var «boxes»;Var «hessian»];
           App «candle_cv_fs_hist_delta_gradient_sign_entry»
             [Num 1;Var «boxes»;Var «hessian»];
           App «candle_cv_fs_hist_delta_gradient_sign_entry»
             [Num 2;Var «boxes»;Var «hessian»];
           App «candle_cv_fs_hist_delta_gradient_sign_entry»
             [Num 3;Var «boxes»;Var «hessian»];
           App «candle_cv_fs_hist_delta_gradient_sign_entry»
             [Num 4;Var «boxes»;Var «hessian»];
           App «candle_cv_fs_hist_delta_gradient_sign_entry»
             [Num 5;Var «boxes»;Var «hessian»]])
        (Let «lower_environment»
          (App «candle_cv_fs_hist_monotone_environment»
            [Num 0;Var «boxes»;Var «gradient»])
          (Let «upper_environment»
            (App «candle_cv_fs_hist_monotone_environment»
              [Num 1;Var «boxes»;Var «gradient»])
            (Let «lower»
              (App «candle_cv_fs_hist_delta_value_block»
                [Var «lower_environment»])
              (Let «upper»
                (App «candle_cv_fs_hist_delta_value_block»
                  [Var «upper_environment»])
                (App «candle_cv_fs_hist_second_make»
                  [Pair (Uop Fst (Var «lower»))
                    (Uop Snd (Var «upper»));
                   Var «gradient»;Var «hessian»]))))))
End

Theorem registered_case10173_fs_hist_delta_second_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_second» =
    SOME ([«boxes»],registered_case10173_fs_hist_delta_second_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_second_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_second» [from_cv boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«boxes»,from_cv boxes)]
        registered_case10173_fs_hist_delta_second_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_second_lookup]
QED

Theorem registered_case10173_fs_hist_delta_second_trace_typed_eval:
  !b0 b1 b2 b3 b4 b5 r0 r1 r2 r3 r4 r5
    g0 g1 g2 g3 g4 g5 hessian lower_environment upper_environment
    lower_value upper_value clock.
    bounded_delta64_hessian [b0;b1;b2;b3;b4;b5] = SOME hessian /\
    bounded_hessian64_rows hessian = SOME [r0;r1;r2;r3;r4;r5] /\
    LENGTH r0 = 6 /\ LENGTH r1 = 6 /\ LENGTH r2 = 6 /\
    LENGTH r3 = 6 /\ LENGTH r4 = 6 /\ LENGTH r5 = 6 /\
    bounded_historical_delta_gradient_box_decimal
      [b0;b1;b2;b3;b4;b5] [0;1;2;3;4;5]
      [r0;r1;r2;r3;r4;r5] = SOME [g0;g1;g2;g3;g4;g5] /\
    bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [g0;g1;g2;g3;g4;g5] F =
      SOME lower_environment /\
    bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [g0;g1;g2;g3;g4;g5] T =
      SOME upper_environment /\
    bounded_historical_delta64_value_decimal lower_environment =
      SOME lower_value /\
    bounded_historical_delta64_value_decimal upper_environment =
      SOME upper_value /\
    180 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_second»
        [from_cv
          (bounded_interval64_object_cv_list [b0;b1;b2;b3;b4;b5])])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv
            (bounded_historical_extreme_interval lower_value upper_value))
          (Pair
            (bounded_interval64_object_cv_list [g0;g1;g2;g3;g4;g5])
            (bounded_interval64_object_cv_matrix
              [r0;r1;r2;r3;r4;r5])))),refs)
Proof
  rpt strip_tac
  >> rw [registered_case10173_fs_hist_delta_second_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_second_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_matrix [r0;r1;r2;r3;r4;r5])`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaHessianEvalTheory.registered_case10173_fs_angle_delta_hessian_compact_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list [g0;g1;g2;g3;g4;g5])`
  >> conj_tac
  >- (irule registered_case10173_fs_hist_delta_gradient_six_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv (bounded_interval64_object_cv_list lower_environment)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss []
          (Q.INST [`upper` |-> `F`]
            compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_monotone_environment_six_result_typed_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv (bounded_interval64_object_cv_list upper_environment)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss []
          (Q.INST [`upper` |-> `T`]
            compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_monotone_environment_six_result_typed_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv lower_value)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaBlockPrimitiveEvalTheory.registered_case10173_fs_hist_delta_value_block_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv upper_value)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaBlockPrimitiveEvalTheory.registered_case10173_fs_hist_delta_value_block_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 7)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_second_make»
            [from_cv
              (bounded_interval64_object_cv
                (bounded_historical_extreme_interval
                  lower_value upper_value));
             from_cv
               (bounded_interval64_object_cv_list
                 [g0;g1;g2;g3;g4;g5]);
             from_cv
               (bounded_interval64_object_cv_matrix
                 [r0;r1;r2;r3;r4;r5])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> Cases_on `lower_value`
      >> Cases_on `upper_value`
      >> simp
           [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_extreme_interval_def,
            compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
            compute_boundedIntervalTheory.bounded_interval64_lower_def,
            compute_boundedIntervalTheory.bounded_interval64_upper_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
      >> simp
           [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_make_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_bounded_delta64_hessian_success_shape:
  bounded_delta64_hessian environment = SOME hessian ==>
  LENGTH environment = 6
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_bounded_hessian64_rows_success_shape:
  bounded_hessian64_rows hessian = SOME rows ==>
  LENGTH rows = 6 /\ EVERY ($= 6 o LENGTH) rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_bounded_historical_delta_gradient_box_decimal_shape:
  !coordinates derivative_rows result.
    bounded_historical_delta_gradient_box_decimal
      environment coordinates derivative_rows = SOME result ==>
    LENGTH coordinates = LENGTH derivative_rows /\
    LENGTH result = LENGTH coordinates
Proof
  Induct_on `coordinates`
  >> Cases_on `derivative_rows`
  >> rw
       [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_box_decimal_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_fs_hist_delta_second_typed_eval:
  !environment value gradient hessian rows clock.
    bounded_historical_delta_second_decimal environment =
      SOME (value,gradient,hessian) /\
    bounded_hessian64_rows hessian = SOME rows /\
    180 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_second»
        [from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv value)
          (Pair (bounded_interval64_object_cv_list gradient)
            (bounded_interval64_object_cv_matrix rows)))),refs)
Proof
  rpt gen_tac
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_second_decimal_source_trace
  >> strip_tac
  >> imp_res_tac registered_case10173_bounded_delta64_hessian_success_shape
  >> imp_res_tac registered_case10173_bounded_hessian64_rows_success_shape
  >> imp_res_tac
       registered_case10173_bounded_historical_delta_gradient_box_decimal_shape
  >> fs []
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_delta_second_trace_typed_eval)
  >> simp []
  >> qexists_tac `hessian`
  >> simp []
QED

val _ = export_theory ();
