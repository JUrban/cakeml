(*****************************************************************************
 * Structural-clock semantics for the authenticated historical raw wrapper.
 *
 * A complete authenticated stream has a fixed 4,173-job shape.  Its
 * canonicality pass therefore costs 108,499 structural units, regardless of
 * the magnitude of the encoded rational numerators and denominators.
 *****************************************************************************)
Theory compute_registeredCase10173RawWrapperStructuralEval
Ancestors
  compute_registeredCase10173RawWrapperEval
  compute_registeredCase10173AuthenticatedStructuralClock
Libs
  bossLib preamble intLib

Theorem registered_case10173_hist_checked_raw_jobs_check_authenticated_structural:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs roots /\
  108500 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv roots])
      (refs:hol_refs) = (M_success (Num 1),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv source_program;from_cv encoded_jobs;from_cv roots]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_hist_checked_raw_jobs_check_unfold]
  >> simp
       [compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_hist_checked_raw_jobs_check_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_bool_and_true_one_eval
  >> simp []
  >> irule
       compute_registeredCase10173RawWrapperEvalTheory.compute_eval_binop_eq_same_result
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> irule
       compute_registeredCase10173CanonicalStructuralEvalTheory.registered_case10173_fso_variable_jobs_canonical_eval_structural
  >> conj_tac
  >- (imp_res_tac
        compute_registeredCase10173AuthenticatedStructuralClockTheory.registered_case10173_authenticated_full_structural_jobs_clock
      >> intLib.ARITH_TAC)
  >> metis_tac
       [compute_boundedCase10173ObjectJobCanonicalTheory.bounded_packed_chars_case10173_decimal_authenticated_full_jobs_canonical]
QED

val _ = export_theory ();
