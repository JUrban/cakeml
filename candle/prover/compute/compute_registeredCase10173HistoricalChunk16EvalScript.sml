(*****************************************************************************
 * Proof-producing evaluation of the genuinely bounded 16-cell case-10173
 * checked-call prefix exported before HOL4 translation.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalChunk16Eval
Ancestors
  compute_evalPure
  compute_registeredCase10173HistoricalChunk16Data
Libs
  bossLib preamble cv_transLib

val _ = cv_trans registered_case10173_historical_chunk16_ceqs_def;
val _ = cv_trans registered_case10173_historical_chunk16_cexp_def;

val registered_case10173_historical_chunk16_pure_eval =
  time cv_eval
    ``compute_eval_pure 100000 registered_case10173_historical_chunk16_ceqs
        registered_case10173_historical_chunk16_cexp``;

val _ = save_thm
  ("registered_case10173_historical_chunk16_pure_eval",
   registered_case10173_historical_chunk16_pure_eval);

Theorem registered_case10173_historical_chunk16_pure_eval_value:
  compute_eval_pure 100000 registered_case10173_historical_chunk16_ceqs
      registered_case10173_historical_chunk16_cexp =
    SOME (from_cv registered_case10173_historical_chunk16_result)
Proof
  simp [registered_case10173_historical_chunk16_pure_eval,
        registered_case10173_historical_chunk16_result_def,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
