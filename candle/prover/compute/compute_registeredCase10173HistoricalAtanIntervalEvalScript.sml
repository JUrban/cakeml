(*****************************************************************************
 * Registered evaluator semantics for the historical arctangent interval.
 *
 * The literal source combines the lower endpoint result at the input lower
 * endpoint with the upper endpoint result at the input upper endpoint.  The
 * theorem below connects that source expression to the authenticated decimal
 * object checker without rebuilding either endpoint proof.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalAtanIntervalEval
Ancestors
  compute_registeredCase10173HistoricalAtanPointEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_atan_interval_body_def:
  registered_case10173_fs_hist_atan_interval_body =
    Pair
      (App «candle_cv_fs_hist_atan_lower_point»
        [Uop Fst (Var «input»)])
      (App «candle_cv_fs_hist_atan_upper_point»
        [Uop Snd (Var «input»)])
End

Theorem registered_case10173_fs_hist_atan_interval_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_atan_interval» =
    SOME ([«input»],registered_case10173_fs_hist_atan_interval_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_atan_interval_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_interval» [from_cv input])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«input»,from_cv input)]
        registered_case10173_fs_hist_atan_interval_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_atan_interval_lookup]
QED

Theorem registered_case10173_fs_hist_atan_interval_endpoints_eval:
  bounded_object_fs_interval64_atan_unit_lower_decimal lower_endpoint =
      SOME lower_result /\
  bounded_object_fs_interval64_atan_unit_upper_decimal upper_endpoint =
      SOME upper_result /\
  32 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_interval»
        [from_cv
          (Pair
            (bounded_signed64_object_cv lower_endpoint)
            (bounded_signed64_object_cv upper_endpoint))])
      (refs:hol_refs) =
    (M_success (from_cv (Pair lower_result upper_result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_atan_interval_unfold]
  >> simp
       [registered_case10173_fs_hist_atan_interval_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- (`compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_lower_point»
          [Uop Fst
            (Pair
              (from_cv (bounded_signed64_object_cv lower_endpoint))
              (from_cv (bounded_signed64_object_cv upper_endpoint)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_lower_point»
          [from_cv (bounded_signed64_object_cv lower_endpoint)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_fs_hist_atan_lower_point_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_upper_point»
          [Uop Snd
            (Pair
              (from_cv (bounded_signed64_object_cv lower_endpoint))
              (from_cv (bounded_signed64_object_cv upper_endpoint)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_upper_point»
          [from_cv (bounded_signed64_object_cv upper_endpoint)]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
  >> rw []
  >> irule
       compute_registeredCase10173HistoricalAtanPointEvalTheory.registered_case10173_fs_hist_atan_upper_point_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_interval_make_valid_some:
  bounded_object_fs_interval_make_valid lower upper = SOME result ==>
  result = Pair lower upper
Proof
  rw
    [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_interval_make_valid_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_fs_hist_atan_interval_eval:
  bounded_object_fs_interval64_atan_unit_decimal input = SOME result /\
  32 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_interval»
        [from_cv (bounded_interval64_object_cv input)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `input`
  >> rename1 `BoundedInterval64 lower_endpoint upper_endpoint`
  >> rpt strip_tac
  >> fs
       [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_interval64_atan_unit_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_fs_interval_make_valid_some
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_atan_interval_endpoints_eval)
  >> simp []
QED

val _ = export_theory ();
