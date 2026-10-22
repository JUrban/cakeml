(*****************************************************************************
 * Proof-producing evaluation of genuine case-10173 cells [2048,2064).      *
 * The aligned job/root chunk is sliced before HOL4 source registration.     *
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalChunkAt2048Count16Eval
Ancestors
  compute_evalPure
  compute_registeredCase10173HistoricalChunkAt2048Count16Data
Libs
  bossLib preamble cv_transLib

val _ = cv_trans registered_case10173_historical_chunk_at2048_count16_ceqs_def;
val _ = cv_trans registered_case10173_historical_chunk_at2048_count16_cexp_def;

val registered_case10173_historical_chunk_at2048_count16_pure_eval =
  time cv_eval
    ``compute_eval_pure 100000
        registered_case10173_historical_chunk_at2048_count16_ceqs
        registered_case10173_historical_chunk_at2048_count16_cexp``;

val _ = save_thm
  ("registered_case10173_historical_chunk_at2048_count16_pure_eval",
   registered_case10173_historical_chunk_at2048_count16_pure_eval);

Theorem registered_case10173_historical_chunk_at2048_count16_pure_eval_value:
  compute_eval_pure 100000
      registered_case10173_historical_chunk_at2048_count16_ceqs
      registered_case10173_historical_chunk_at2048_count16_cexp =
    SOME
      (from_cv
        registered_case10173_historical_chunk_at2048_count16_result)
Proof
  simp
    [registered_case10173_historical_chunk_at2048_count16_pure_eval,
     registered_case10173_historical_chunk_at2048_count16_result_def,
     compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
