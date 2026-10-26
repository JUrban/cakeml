(*****************************************************************************
 * Positive and fail-closed identity tests for the corrected production
 * dispatcher.  These are structural tests only: they do not replay the
 * numerical certificate.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10ProductionDispatchTest
Ancestors
  compute_registeredCase10173Tag10GenuineAuthenticatedFast
  compute_registeredCase10173Tag10DataIdentity
Libs
  bossLib preamble

Theorem registered_case10173_tag10_genuine_fast_eval_rejects_old_ceqs:
  registered_case10173_tag10_genuine_decimal_authenticated_fast_eval
    registered_case10173_historical_chunk16_ceqs expression = NONE
Proof
  simp
    [compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def,
     compute_registeredCase10173Tag10DataIdentityTheory.registered_case10173_old_and_tag10_equations_differ]
QED

Theorem registered_case10173_tag10_genuine_fast_eval_rejects_wrong_entry:
  wrong_entry <> «candle_cv_case10173_hist_checked_raw_jobs_check» ==>
  registered_case10173_tag10_genuine_decimal_authenticated_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (App wrong_entry
      [from_cv source_program;from_cv encoded_jobs;from_cv encoded_roots]) = NONE
Proof
  simp
    [compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def,
     compute_payload3FastTheory.compute_literal_call_payload3_def]
QED

Theorem registered_case10173_tag10_genuine_fast_eval_rejects_wrong_source:
  source_program <> registered_case10173_genuine_source_program ==>
  registered_case10173_tag10_genuine_decimal_authenticated_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_checked_raw_jobs_check»
      [from_cv source_program;from_cv encoded_jobs;from_cv encoded_roots]) = NONE
Proof
  simp
    [compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def,
     compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_packed_certificate_bytes_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def]
QED

Theorem registered_case10173_tag10_genuine_fast_eval_rejects_unauthenticated_payload:
  ~bounded_packed_chars_case10173_decimal_authenticated_full_check
      (mlstring$explode registered_case10173_genuine_packed_certificate)
      encoded_jobs encoded_roots ==>
  registered_case10173_tag10_genuine_decimal_authenticated_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_checked_raw_jobs_check»
      [from_cv registered_case10173_genuine_source_program;
       from_cv encoded_jobs;from_cv encoded_roots]) = NONE
Proof
  simp
    [compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def,
     compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_packed_certificate_bytes_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def,
     compute_payload3FastTheory.compute_payload3_call_fast_eval_def]
QED

val _ = export_theory ();
