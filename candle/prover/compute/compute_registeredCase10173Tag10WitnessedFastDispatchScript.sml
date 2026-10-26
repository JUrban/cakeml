(*****************************************************************************
 * Data-driven case-10173 dispatch.
 *
 * The packed certificate is a literal witness in the compute term, rather
 * than a value closed over by the evaluator or installed in candle_kernelProg.
 * The ordinary meaning remains the unchanged three-argument raw checker.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10WitnessedFastDispatch
Ancestors
  compute_witnessedPayload3Fast
  compute_cvPackedBytes
  compute_registeredCase10173Tag10AuthenticatedFastDispatch
  compute_registeredCase10173Tag10AuthenticatedFastFullEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_tag10_decimal_authenticated_fast_raw_predecessor_eval:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots ==>
  compute_eval (compute_default_clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv registered_case10173_genuine_source_program;
         from_cv encoded_jobs;from_cv encoded_roots])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173Tag10RawWrapperStructuralEvalTheory.registered_case10173_tag10_hist_checked_raw_jobs_check_authenticated_structural
  >> conj_tac
  >- simp [computeTheory.compute_default_clock]
  >> conj_tac
  >- (irule
       compute_registeredCase10173Tag10AuthenticatedFastFullEvalTheory.registered_case10173_tag10_decimal_authenticated_fast_full_eval
      >> conj_tac >- simp [computeTheory.compute_default_clock]
      >> qexists_tac `bytes`
      >> asm_rewrite_tac [])
  >> qexists_tac `bytes`
  >> asm_rewrite_tac []
QED

Definition registered_case10173_tag10_witnessed_checker_def:
  registered_case10173_tag10_witnessed_checker
      certificate source_program encoded_jobs encoded_roots <=>
    case cv_unpack_byte_chunks certificate of
    | NONE => F
    | SOME bytes =>
        registered_case10173_tag10_decimal_authenticated_fast_checker
          bytes source_program encoded_jobs encoded_roots
End

Theorem registered_case10173_tag10_witnessed_fast_checker_refines:
  compute_witnessed_payload3_refines
    registered_case10173_historical_chunk16_tag10_ceqs
    «candle_cv_case10173_hist_checked_raw_jobs_check»
    registered_case10173_tag10_witnessed_checker
Proof
  rw
    [compute_witnessedPayload3FastTheory.compute_witnessed_payload3_refines_def,
     registered_case10173_tag10_witnessed_checker_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> gvs []
  >> metis_tac
       [registered_case10173_tag10_decimal_authenticated_fast_raw_predecessor_eval]
QED

Definition registered_case10173_tag10_witnessed_fast_eval_def:
  registered_case10173_tag10_witnessed_fast_eval =
    compute_witnessed_payload3_fast_eval
      registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_nl_certificate_witness»
      «candle_cv_case10173_hist_checked_raw_jobs_check»
      registered_case10173_tag10_witnessed_checker
End

Theorem registered_case10173_tag10_witnessed_fast_eval_ok:
  compute_fast_eval_ok registered_case10173_tag10_witnessed_fast_eval
Proof
  rw [registered_case10173_tag10_witnessed_fast_eval_def]
  >> irule
       compute_witnessedPayload3FastTheory.compute_witnessed_payload3_fast_eval_ok
  >> ACCEPT_TAC registered_case10173_tag10_witnessed_fast_checker_refines
QED

Theorem registered_case10173_tag10_witnessed_fast_eval_hit:
  registered_case10173_tag10_witnessed_checker
      certificate source_program encoded_jobs encoded_roots ==>
  registered_case10173_tag10_witnessed_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (Let «candle_cv_nl_certificate_witness» (from_cv certificate)
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv encoded_roots])) =
    SOME (Num 1)
Proof
  simp
    [registered_case10173_tag10_witnessed_fast_eval_def,
     compute_witnessedPayload3FastTheory.compute_witnessed_payload3_fast_eval_def]
QED

Theorem registered_case10173_tag10_witnessed_fast_eval_rejects_old_ceqs:
  registered_case10173_historical_chunk16_ceqs <>
      registered_case10173_historical_chunk16_tag10_ceqs ==>
  registered_case10173_tag10_witnessed_fast_eval
    registered_case10173_historical_chunk16_ceqs expression = NONE
Proof
  simp
    [registered_case10173_tag10_witnessed_fast_eval_def,
     compute_witnessedPayload3FastTheory.compute_witnessed_payload3_fast_eval_def]
QED

Theorem registered_case10173_tag10_witnessed_fast_eval_rejects_wrong_source:
  source_program <> registered_case10173_genuine_source_program ==>
  registered_case10173_tag10_witnessed_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (Let «candle_cv_nl_certificate_witness» (from_cv certificate)
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv encoded_roots])) =
    NONE
Proof
  simp
    [registered_case10173_tag10_witnessed_fast_eval_def,
     compute_witnessedPayload3FastTheory.compute_witnessed_payload3_fast_eval_def,
     registered_case10173_tag10_witnessed_checker_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def]
  >> every_case_tac
  >> simp []
QED

Theorem registered_case10173_tag10_witnessed_fast_eval_rejects_bad_certificate:
  cv_unpack_byte_chunks certificate = NONE ==>
  registered_case10173_tag10_witnessed_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (Let «candle_cv_nl_certificate_witness» (from_cv certificate)
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv registered_case10173_genuine_source_program;
         from_cv encoded_jobs;from_cv encoded_roots])) = NONE
Proof
  simp
    [registered_case10173_tag10_witnessed_fast_eval_def,
     compute_witnessedPayload3FastTheory.compute_witnessed_payload3_fast_eval_def,
     registered_case10173_tag10_witnessed_checker_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def]
QED

Theorem registered_case10173_tag10_witnessed_fast_eval_rejects_bad_decoded_certificate:
  cv_unpack_byte_chunks certificate = SOME bytes /\
  ~bounded_packed_chars_case10173_decimal_authenticated_full_check
      bytes encoded_jobs encoded_roots ==>
  registered_case10173_tag10_witnessed_fast_eval
    registered_case10173_historical_chunk16_tag10_ceqs
    (Let «candle_cv_nl_certificate_witness» (from_cv certificate)
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv registered_case10173_genuine_source_program;
         from_cv encoded_jobs;from_cv encoded_roots])) = NONE
Proof
  simp
    [registered_case10173_tag10_witnessed_fast_eval_def,
     compute_witnessedPayload3FastTheory.compute_witnessed_payload3_fast_eval_def,
     registered_case10173_tag10_witnessed_checker_def,
     compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def]
QED

val _ = export_theory ();
