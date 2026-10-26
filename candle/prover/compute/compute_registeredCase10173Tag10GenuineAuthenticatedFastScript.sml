(*****************************************************************************
 * Closed production evaluator for the first genuine case-10173 certificate
 * using the corrected private historical opcode (tag 10).
 *
 * The generated mlstring is only a compact immutable carrier.  Its bytes are
 * untrusted until the complete authenticated checker has related every
 * packet to the literal source jobs and historical root records.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10GenuineAuthenticatedFast
Ancestors
  compute_registeredCase10173Tag10AuthenticatedFastDispatch
  compute_registeredCase10173GenuineCertificateData
Libs
  bossLib preamble

Definition registered_case10173_tag10_genuine_packed_certificate_bytes_def:
  registered_case10173_tag10_genuine_packed_certificate_bytes =
    mlstring$explode registered_case10173_genuine_packed_certificate
End

Definition registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def:
  registered_case10173_tag10_genuine_decimal_authenticated_fast_eval =
    registered_case10173_tag10_decimal_authenticated_fast_eval
      registered_case10173_tag10_genuine_packed_certificate_bytes
End

Theorem registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_ok:
  compute_fast_eval_ok
    registered_case10173_tag10_genuine_decimal_authenticated_fast_eval
Proof
  PURE_REWRITE_TAC
    [registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def,
     registered_case10173_tag10_genuine_packed_certificate_bytes_def]
  >> MATCH_ACCEPT_TAC
       compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_ok
QED

Theorem registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_hit:
  registered_case10173_tag10_decimal_authenticated_fast_checker
      (mlstring$explode
        registered_case10173_genuine_packed_certificate)
      registered_case10173_genuine_source_program encoded_jobs encoded_roots
  ==>
  registered_case10173_tag10_genuine_decimal_authenticated_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_checked_raw_jobs_check»
      [from_cv registered_case10173_genuine_source_program;
       from_cv encoded_jobs;from_cv encoded_roots]) = SOME (Num 1)
Proof
  PURE_REWRITE_TAC
    [registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def,
     registered_case10173_tag10_genuine_packed_certificate_bytes_def]
  >> MATCH_ACCEPT_TAC
       compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_hit
QED

val _ = export_theory ();
