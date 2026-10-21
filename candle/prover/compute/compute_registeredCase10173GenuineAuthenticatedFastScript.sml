(*****************************************************************************
 * Closed production evaluator for the first genuine case-10173 certificate.
 *
 * The generated mlstring is only a compact immutable carrier.  Its bytes are
 * untrusted until the complete authenticated checker has related every
 * packet to the literal source jobs and historical root records.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineAuthenticatedFast
Ancestors
  compute_registeredCase10173AuthenticatedFastDispatch
  compute_registeredCase10173GenuineCertificateData
Libs
  bossLib preamble

Definition registered_case10173_genuine_decimal_authenticated_fast_eval_def:
  registered_case10173_genuine_decimal_authenticated_fast_eval =
    registered_case10173_decimal_authenticated_fast_eval
      (mlstring$explode
        registered_case10173_genuine_packed_certificate)
End

Theorem registered_case10173_genuine_decimal_authenticated_fast_eval_ok:
  compute_fast_eval_ok
    registered_case10173_genuine_decimal_authenticated_fast_eval
Proof
  PURE_REWRITE_TAC
    [registered_case10173_genuine_decimal_authenticated_fast_eval_def]
  >> MATCH_ACCEPT_TAC
       compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_eval_ok
QED

Theorem registered_case10173_genuine_decimal_authenticated_fast_eval_hit:
  registered_case10173_decimal_authenticated_fast_checker
      (mlstring$explode
        registered_case10173_genuine_packed_certificate)
      registered_case10173_genuine_source_program encoded_jobs encoded_roots
  ==>
  registered_case10173_genuine_decimal_authenticated_fast_eval
    registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_case10173_hist_checked_raw_jobs_check»
      [from_cv registered_case10173_genuine_source_program;
       from_cv encoded_jobs;from_cv encoded_roots]) = SOME (Num 1)
Proof
  PURE_REWRITE_TAC
    [registered_case10173_genuine_decimal_authenticated_fast_eval_def]
  >> MATCH_ACCEPT_TAC
       compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_eval_hit
QED

val _ = export_theory ();
