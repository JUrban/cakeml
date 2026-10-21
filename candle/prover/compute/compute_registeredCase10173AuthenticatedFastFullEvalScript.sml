(*****************************************************************************
 * Whole-stream ordinary semantics for the authenticated fast case-10173
 * checker.
 *
 * The local packet theorem is independent of the genuine stream length.
 * This theory composes it with the already-proved 4,173-record recursion and
 * with the structural-clock raw wrapper.  The only remaining data premise is
 * acceptance by the full packed authenticator; no per-cell source replay is
 * used by either theorem below.
 *****************************************************************************)
Theory compute_registeredCase10173AuthenticatedFastFullEval
Ancestors
  compute_registeredCase10173AuthenticatedFastHeadEval
  compute_registeredCase10173RawWrapperStructuralEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_decimal_authenticated_fast_full_eval:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots /\
  20012519 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv registered_case10173_genuine_source_program;
         from_cv encoded_jobs;from_cv encoded_roots])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AuthenticatedEvalTheory.registered_case10173_decimal_authenticated_full_eval
  >> conj_tac
  >- (qexists_tac `20000000`
      >> conj_tac >- intLib.ARITH_TAC
      >> ACCEPT_TAC
           compute_registeredCase10173AuthenticatedFastHeadEvalTheory.registered_case10173_decimal_authenticated_fast_head_refines)
  >> qexists_tac `bytes`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_decimal_authenticated_fast_full_default_eval:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots ==>
  compute_eval compute_default_clock
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_jobs_check»
        [from_cv registered_case10173_genuine_source_program;
         from_cv encoded_jobs;from_cv encoded_roots])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule registered_case10173_decimal_authenticated_fast_full_eval
  >> conj_tac >- simp [computeTheory.compute_default_clock]
  >> qexists_tac `bytes`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_decimal_authenticated_fast_raw_default_eval:
  bounded_packed_chars_case10173_decimal_authenticated_full_check bytes
      encoded_jobs encoded_roots ==>
  compute_eval compute_default_clock
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_checked_raw_jobs_check»
        [from_cv registered_case10173_genuine_source_program;
         from_cv encoded_jobs;from_cv encoded_roots])
      (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173RawWrapperStructuralEvalTheory.registered_case10173_hist_checked_raw_jobs_check_authenticated_structural
  >> conj_tac >- simp [computeTheory.compute_default_clock]
  >> conj_tac
  >- (irule registered_case10173_decimal_authenticated_fast_full_eval
      >> conj_tac >- simp [computeTheory.compute_default_clock]
      >> qexists_tac `bytes`
      >> asm_rewrite_tac [])
  >> qexists_tac `bytes`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
