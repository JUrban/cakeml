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

val _ = export_theory ();
