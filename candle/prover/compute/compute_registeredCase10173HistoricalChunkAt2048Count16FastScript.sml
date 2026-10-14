(*****************************************************************************
 * Exact fast-evaluator registration for genuine cells [2048,2064).         *
 *                                                                           *
 * The one-time pure-evaluator theorem authorizes this exact equation/call   *
 * identity.  A production hit can therefore return the registered result   *
 * without repeating the generic evaluator.                                 *
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalChunkAt2048Count16Fast
Ancestors
  compute_registeredCase10173HistoricalChunkAt2048Count16Eval
Libs
  bossLib preamble

Definition registered_case10173_historical_chunk_at2048_count16_fast_eval_def:
  registered_case10173_historical_chunk_at2048_count16_fast_eval ceqs cexp =
    if ceqs = registered_case10173_historical_chunk_at2048_count16_ceqs /\
       cexp = registered_case10173_historical_chunk_at2048_count16_cexp
    then SOME registered_case10173_historical_chunk_at2048_count16_result
    else NONE
End

Theorem registered_case10173_historical_chunk_at2048_count16_compute_eval:
  !s.
    compute_eval compute_default_clock
      registered_case10173_historical_chunk_at2048_count16_ceqs
      registered_case10173_historical_chunk_at2048_count16_cexp s =
    (M_success
       (from_cv
         registered_case10173_historical_chunk_at2048_count16_result),s)
Proof
  gen_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `100000`
  >> simp
       [computeTheory.compute_default_clock,
        registered_case10173_historical_chunk_at2048_count16_pure_eval_value]
QED

Theorem registered_case10173_historical_chunk_at2048_count16_fast_eval_ok:
  compute_fast_eval_ok
    registered_case10173_historical_chunk_at2048_count16_fast_eval
Proof
  rw
    [computeTheory.compute_fast_eval_ok_def,
     registered_case10173_historical_chunk_at2048_count16_fast_eval_def]
  >> every_case_tac
  >> gvs
       [registered_case10173_historical_chunk_at2048_count16_compute_eval]
QED

val _ = export_theory ();
