(*****************************************************************************
 * Focused positive/negative identity probe for the corrected private
 * historical opcode.  This deliberately performs no numerical certificate
 * evaluation: it checks the fail-closed equation-identity seam before any
 * wider proof or runtime rebuild is permitted.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10DispatchProbe
Ancestors
  compute_registeredCase10173AuthenticatedFastDispatch
  compute_registeredCase10173HistoricalChunk16Tag10Data
Libs
  bossLib preamble

Definition registered_case10173_tag10_fast_eval_def:
  registered_case10173_tag10_fast_eval bytes =
    compute_payload3_call_fast_eval
      registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_checked_raw_jobs_check»
      (registered_case10173_decimal_authenticated_fast_checker bytes)
End

Theorem registered_case10173_tag10_fast_eval_hit:
  registered_case10173_decimal_authenticated_fast_checker
      bytes registered_case10173_genuine_source_program
      encoded_jobs encoded_roots ==>
  registered_case10173_tag10_fast_eval bytes
    registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_checked_raw_jobs_check»
      [from_cv registered_case10173_genuine_source_program;
       from_cv encoded_jobs;from_cv encoded_roots]) = SOME (Num 1)
Proof
  simp
    [registered_case10173_tag10_fast_eval_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def]
QED

Theorem registered_case10173_old_and_tag10_ceqs_differ:
  registered_case10173_historical_chunk16_ceqs <>
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  EVAL_TAC
QED

Theorem registered_case10173_old_fast_eval_rejects_tag10_ceqs:
  registered_case10173_decimal_authenticated_fast_eval bytes
    registered_case10173_historical_chunk16_tag10_ceqs expression = NONE
Proof
  simp
    [compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_eval_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def,
     registered_case10173_old_and_tag10_ceqs_differ]
QED

val _ = export_theory ();
