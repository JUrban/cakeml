(*****************************************************************************
 * Packet-independent evaluator refinement for the historical delta_x4
 * center value.
 *
 * The first genuine-job proof originally closed this call by evaluating the
 * first packet's constants.  The authenticated batch needs the same result
 * for an arbitrary successful decimal packet.  This theorem derives every
 * registered object operation from the successful decimal calculation, so
 * it can be reused by the packet-parametric first-order evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaX4GeneralEval
Ancestors
  compute_registeredCase10173HistoricalFirstOrderCenterEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_bounded_interval64_object_cv_list_six:
  bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5] =
    registered_case10173_cv_list
      [bounded_interval64_object_cv x0;
       bounded_interval64_object_cv x1;
       bounded_interval64_object_cv x2;
       bounded_interval64_object_cv x3;
       bounded_interval64_object_cv x4;
       bounded_interval64_object_cv x5]
Proof
  simp
    [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_historical_delta_x4_value_decimal_eval:
  bounded_historical_delta_x4_value_decimal [x0;x1;x2;x3;x4;x5] =
      SOME result /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value»
        [from_cv
          (bounded_interval64_object_cv_list
            [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> once_rewrite_tac
       [registered_case10173_bounded_interval64_object_cv_list_six]
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_hist_delta_x4_value_trace_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> fs []
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_historical_delta_x4_value_environment_eval:
  bounded_historical_delta_x4_value_decimal environment = SOME result /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value»
        [from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def]
  >> every_case_tac
  >> gvs []
  >> irule registered_case10173_historical_delta_x4_value_decimal_eval
  >> simp
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def]
QED

val _ = export_theory ();
