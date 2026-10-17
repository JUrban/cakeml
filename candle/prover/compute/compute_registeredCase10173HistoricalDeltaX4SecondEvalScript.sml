(*****************************************************************************
 * Registered source refinement for the historical delta_x4 second-order jet.
 *
 * The literal gradient groups its two negative terms before the six-way sum,
 * whereas the typed checker accumulates the original eight terms.  The first
 * theorem below relates those source orders through their exact endpoint
 * semantics and then reuses the registered trace evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4SecondEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4ValueBlockEval
  compute_registeredCase10173HistoricalSecondOrderPrimitiveEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_hist_delta_x4_gradient_typed_eval:
  !x0 x1 x2 x3 x4 x5 gradient clock.
    bounded_historical_delta_x4_gradient [x0;x1;x2;x3;x4;x5] =
        SOME gradient /\
    25 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_delta_x4_gradient»
          [from_cv
            (bounded_interval64_object_cv_list
              [x0;x1;x2;x3;x4;x5])])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_list gradient)),refs)
Proof
  rpt gen_tac
  >> strip_tac
  >> fs
       [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_interval64_sum
          [x0;x2;bounded_interval64_neg x4] = SOME g5`
  >> rename1
       `bounded_interval64_sum
          [x0;x1;bounded_interval64_neg x5] = SOME g4`
  >> rename1
       `bounded_historical_scale2 (bounded_interval64_neg x0) = SOME g3`
  >> rename1
       `bounded_interval64_sum
          [x0;bounded_interval64_neg x1;x5] = SOME g2`
  >> rename1
       `bounded_interval64_sum
          [x0;bounded_interval64_neg x2;x4] = SOME g1`
  >> rename1
       `bounded_interval64_sum
          [bounded_interval64_neg x0;bounded_interval64_neg x0;
           x1;x2;bounded_interval64_neg x3;bounded_interval64_neg x3;
           x4;x5] = SOME g0`
  >> `registered_case10173_fs_interval_scale_neg_two_object
        (bounded_interval64_object_cv x0) =
      SOME (bounded_interval64_object_cv g3)` by
       (irule registered_case10173_interval_scale_neg_two_object_typed_exact
        >> fs
             [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def])
  >> mp_tac
       (Q.SPEC `x3`
          registered_case10173_interval_scale_neg_two_object_ints_exists)
  >> disch_then (qx_choose_then `negative_two_x3` strip_assume_tac)
  >> `bounded_interval64_add
        (bounded_interval64_neg x0) (bounded_interval64_neg x0) =
      SOME g3` by
       fs
         [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def]
  >> imp_res_tac compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> imp_res_tac bounded_interval64_sum_endpoint_values
  >> imp_res_tac bounded_interval64_sum_valid
  >> `registered_case10173_interval_ints_sum
        [bounded_interval64_object_cv g3;
         bounded_interval64_object_cv x1;
         bounded_interval64_object_cv x2;
         negative_two_x3;
         bounded_interval64_object_cv x4;
         bounded_interval64_object_cv x5] =
      SOME
        (bounded_signed64_to_int (bounded_interval64_lower g0),
         bounded_signed64_to_int (bounded_interval64_upper g0))` by
       (fs
          [registered_case10173_interval_ints_sum_def,
           compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_object_cv,
           compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_value]
        >> fs [compute_boundedIntervalAddTheory.bounded_interval64_neg_value]
        >> intLib.ARITH_TAC)
  >> `registered_case10173_fs_interval_sum_object
        [bounded_interval64_object_cv g3;
         bounded_interval64_object_cv x1;
         bounded_interval64_object_cv x2;
         negative_two_x3;
         bounded_interval64_object_cv x4;
         bounded_interval64_object_cv x5] =
      SOME (bounded_interval64_object_cv g0)` by
       (irule registered_case10173_interval_sum_object_target_exact
        >> simp [])
  >> `registered_case10173_fs_interval_sum_object
        [bounded_interval64_object_cv x0;
         bounded_interval64_object_cv (bounded_interval64_neg x2);
         bounded_interval64_object_cv x4] =
      SOME (bounded_interval64_object_cv g1)` by
       (irule registered_case10173_interval_sum_object_target_exact
        >> fs [])
  >> `registered_case10173_fs_interval_sum_object
        [bounded_interval64_object_cv x0;
         bounded_interval64_object_cv (bounded_interval64_neg x1);
         bounded_interval64_object_cv x5] =
      SOME (bounded_interval64_object_cv g2)` by
       (irule registered_case10173_interval_sum_object_target_exact
        >> fs [])
  >> `registered_case10173_fs_interval_sum_object
        [bounded_interval64_object_cv x0;
         bounded_interval64_object_cv x1;
         bounded_interval64_object_cv (bounded_interval64_neg x5)] =
      SOME (bounded_interval64_object_cv g4)` by
       (irule registered_case10173_interval_sum_object_target_exact
        >> fs [])
  >> `registered_case10173_fs_interval_sum_object
        [bounded_interval64_object_cv x0;
         bounded_interval64_object_cv x2;
         bounded_interval64_object_cv (bounded_interval64_neg x4)] =
      SOME (bounded_interval64_object_cv g5)` by
       (irule registered_case10173_interval_sum_object_target_exact
        >> fs [])
  >> once_rewrite_tac
       [GSYM
          compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv]
  >> simp []
  >> irule
       compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_hist_delta_x4_gradient_trace_eval
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
  >> metis_tac []
QED

Theorem bounded_historical_delta_x4_gradient_environment_shape:
  !environment gradient.
    bounded_historical_delta_x4_gradient environment = SOME gradient ==>
    ?x0 x1 x2 x3 x4 x5.
      environment = [x0;x1;x2;x3;x4;x5]
Proof
  rpt gen_tac
  >> rw
       [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem registered_case10173_fs_hist_delta_x4_gradient_list_typed_eval:
  !environment gradient clock.
    bounded_historical_delta_x4_gradient environment = SOME gradient /\
    25 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_delta_x4_gradient»
          [from_cv (bounded_interval64_object_cv_list environment)])
        (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_list gradient)),refs)
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac bounded_historical_delta_x4_gradient_environment_shape
  >> gvs []
  >> irule registered_case10173_fs_hist_delta_x4_gradient_typed_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_monotone_environment_six_result_typed_eval:
  bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [d0;d1;d2;d3;d4;d5] upper =
        SOME result /\
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_monotone_environment»
        [Num (if upper then 1 else 0);
         from_cv
           (bounded_interval64_object_cv_list [b0;b1;b2;b3;b4;b5]);
         from_cv
           (bounded_interval64_object_cv_list [d0;d1;d2;d3;d4;d5])])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> gvs
       [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_environment_def]
  >> irule
       compute_registeredCase10173HistoricalMonotoneEvalTheory.registered_case10173_fs_hist_monotone_environment_six_typed_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_delta_x4_value_block_typed_eval:
  !environment result clock.
    bounded_historical_delta_x4_value_block_decimal environment =
        SOME result /\
    29 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_delta_x4_value_block»
          [from_cv (bounded_interval64_object_cv_list environment)])
        (refs:hol_refs) =
      (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt gen_tac
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv]
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_fs_hist_delta_x4_value_block_object_eval
  >> conj_tac >- simp []
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_fs_hist_delta_x4_value_block_object_typed_exact
  >> simp []
QED

Definition registered_case10173_fs_hist_delta_x4_second_body_def:
  registered_case10173_fs_hist_delta_x4_second_body =
    Let «gradient»
      (App «candle_cv_fs_hist_delta_x4_gradient» [Var «boxes»])
      (Let «hessian»
        (App «candle_cv_fs_hist_delta_x4_hessian» [])
        (Let «lower_environment»
          (App «candle_cv_fs_hist_monotone_environment»
            [Num 0;Var «boxes»;Var «gradient»])
          (Let «upper_environment»
            (App «candle_cv_fs_hist_monotone_environment»
              [Num 1;Var «boxes»;Var «gradient»])
            (Let «lower»
              (App «candle_cv_fs_hist_delta_x4_value_block»
                [Var «lower_environment»])
              (Let «upper»
                (App «candle_cv_fs_hist_delta_x4_value_block»
                  [Var «upper_environment»])
                (App «candle_cv_fs_hist_second_make»
                  [Pair (Uop Fst (Var «lower»))
                    (Uop Snd (Var «upper»));
                   Var «gradient»;Var «hessian»]))))))
End

Theorem registered_case10173_fs_hist_delta_x4_second_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_delta_x4_second» =
    SOME ([«boxes»],registered_case10173_fs_hist_delta_x4_second_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_delta_x4_second_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_second» [from_cv boxes])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«boxes»,from_cv boxes)]
        registered_case10173_fs_hist_delta_x4_second_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_delta_x4_second_lookup]
QED

Theorem registered_case10173_fs_hist_delta_x4_second_trace_typed_eval:
  !b0 b1 b2 b3 b4 b5 d0 d1 d2 d3 d4 d5
    hessian rows lower_environment upper_environment
    lower_value upper_value clock.
    bounded_historical_delta_x4_gradient [b0;b1;b2;b3;b4;b5] =
      SOME [d0;d1;d2;d3;d4;d5] /\
    bounded_historical_delta_x4_hessian_decimal = SOME hessian /\
    bounded_hessian64_rows hessian = SOME rows /\
    bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [d0;d1;d2;d3;d4;d5] F =
      SOME lower_environment /\
    bounded_historical_monotone_environment
      [b0;b1;b2;b3;b4;b5] [d0;d1;d2;d3;d4;d5] T =
      SOME upper_environment /\
    bounded_historical_delta_x4_value_block_decimal lower_environment =
      SOME lower_value /\
    bounded_historical_delta_x4_value_block_decimal upper_environment =
      SOME upper_value /\
    40 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_second»
        [from_cv
          (bounded_interval64_object_cv_list [b0;b1;b2;b3;b4;b5])])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv
            (bounded_historical_extreme_interval lower_value upper_value))
          (Pair
            (bounded_interval64_object_cv_list [d0;d1;d2;d3;d4;d5])
            (bounded_interval64_object_cv_matrix rows)))),refs)
Proof
  rpt strip_tac
  >> rw [registered_case10173_fs_hist_delta_x4_second_unfold]
  >> simp
       [registered_case10173_fs_hist_delta_x4_second_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv_list [d0;d1;d2;d3;d4;d5])`
  >> conj_tac
  >- (irule registered_case10173_fs_hist_delta_x4_gradient_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv_matrix rows)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4HessianEvalTheory.registered_case10173_fs_hist_delta_x4_hessian_typed_eval
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
            registered_case10173_fs_hist_monotone_environment_six_result_typed_eval))
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
            registered_case10173_fs_hist_monotone_environment_six_result_typed_eval))
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
  >- (irule registered_case10173_fs_hist_delta_x4_value_block_typed_eval
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
  >- (irule registered_case10173_fs_hist_delta_x4_value_block_typed_eval
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
                 [d0;d1;d2;d3;d4;d5]);
             from_cv (bounded_interval64_object_cv_matrix rows)]) refs`
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

Theorem registered_case10173_fs_hist_delta_x4_second_typed_eval:
  !environment value gradient hessian rows clock.
    bounded_historical_delta_x4_second_decimal environment =
      SOME (value,gradient,hessian) /\
    bounded_hessian64_rows hessian = SOME rows /\
    40 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_second»
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
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_x4_second_decimal_source_trace
  >> strip_tac
  >> imp_res_tac bounded_historical_delta_x4_gradient_environment_shape
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_delta_x4_gradient_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_delta_x4_second_trace_typed_eval)
  >> simp []
  >> qexists_tac `hessian`
  >> simp []
QED

val _ = export_theory ();
