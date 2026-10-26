(*****************************************************************************
 * Registered fast-dispatch contract for the complete authenticated
 * case-10173 stream.
 *
 * The certificate byte stream is captured by the checker closure.  The
 * three payloads remain the unchanged source program, source jobs, and
 * historical roots from the literal registered call.  A hit is therefore
 * possible only after the complete packed authenticator accepts those exact
 * payloads; the result is justified by the default-clock full-stream theorem
 * rather than by replaying the generic evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10AuthenticatedFastDispatch
Ancestors
  compute_payload3Fast
  compute_registeredCase10173Tag10AuthenticatedFastFullEval
Libs
  bossLib preamble

Definition registered_case10173_tag10_decimal_authenticated_fast_checker_def:
  registered_case10173_tag10_decimal_authenticated_fast_checker
      bytes source_program encoded_jobs encoded_roots <=>
    source_program = registered_case10173_genuine_source_program /\
    bounded_packed_chars_case10173_decimal_authenticated_full_check
      bytes encoded_jobs encoded_roots
End

Theorem registered_case10173_tag10_decimal_authenticated_fast_checker_refines:
  compute_payload3_call_refines
    registered_case10173_historical_chunk16_tag10_ceqs
    «candle_cv_case10173_hist_checked_raw_jobs_check»
    (registered_case10173_tag10_decimal_authenticated_fast_checker bytes)
Proof
  rw
    [compute_payload3FastTheory.compute_payload3_call_refines_def,
     registered_case10173_tag10_decimal_authenticated_fast_checker_def]
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> gvs []
  >> irule
       compute_registeredCase10173Tag10AuthenticatedFastFullEvalTheory.registered_case10173_tag10_decimal_authenticated_fast_raw_default_eval
  >> qexists_tac `bytes`
  >> asm_rewrite_tac []
QED

Definition registered_case10173_tag10_decimal_authenticated_fast_eval_def:
  registered_case10173_tag10_decimal_authenticated_fast_eval bytes =
    compute_payload3_call_fast_eval
      registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_checked_raw_jobs_check»
      (registered_case10173_tag10_decimal_authenticated_fast_checker bytes)
End

Theorem registered_case10173_tag10_decimal_authenticated_fast_eval_ok:
  compute_fast_eval_ok
    (registered_case10173_tag10_decimal_authenticated_fast_eval bytes)
Proof
  rw [registered_case10173_tag10_decimal_authenticated_fast_eval_def]
  >> irule compute_payload3FastTheory.compute_payload3_call_fast_eval_ok
  >> ACCEPT_TAC
       registered_case10173_tag10_decimal_authenticated_fast_checker_refines
QED

Theorem registered_case10173_tag10_decimal_authenticated_fast_eval_hit:
  registered_case10173_tag10_decimal_authenticated_fast_checker
      bytes registered_case10173_genuine_source_program
      encoded_jobs encoded_roots ==>
  registered_case10173_tag10_decimal_authenticated_fast_eval bytes
    registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_checked_raw_jobs_check»
      [from_cv registered_case10173_genuine_source_program;
       from_cv encoded_jobs;from_cv encoded_roots]) = SOME (Num 1)
Proof
  simp
    [registered_case10173_tag10_decimal_authenticated_fast_eval_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def]
QED

val _ = export_theory ();
