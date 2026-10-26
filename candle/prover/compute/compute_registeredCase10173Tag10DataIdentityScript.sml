(*****************************************************************************
 * Focused identity split for the corrected tag-10 registration data.
 *
 * The input expression is unchanged: only the evaluator equation environment
 * changes.  Keeping that fact explicit permits the already proved input and
 * certificate bindings to remain reusable while the tag-sensitive evaluator
 * trace is rebuilt additively.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10DataIdentity
Ancestors
  compute_registeredCase10173HistoricalChunk16Data
  compute_registeredCase10173HistoricalChunk16Tag10Data
Libs
  bossLib preamble

Theorem registered_case10173_old_and_tag10_input_equal:
  registered_case10173_historical_chunk16_tag10_cexp =
    registered_case10173_historical_chunk16_cexp
Proof
  rw
    [compute_registeredCase10173HistoricalChunk16Tag10DataTheory.registered_case10173_historical_chunk16_tag10_cexp_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def]
QED

Theorem registered_case10173_old_and_tag10_expected_result_equal:
  registered_case10173_historical_chunk16_tag10_result =
    registered_case10173_historical_chunk16_result
Proof
  rw
    [compute_registeredCase10173HistoricalChunk16Tag10DataTheory.registered_case10173_historical_chunk16_tag10_result_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_result_def]
QED

Theorem registered_case10173_old_and_tag10_equations_differ:
  registered_case10173_historical_chunk16_tag10_ceqs <>
    registered_case10173_historical_chunk16_ceqs
Proof
  EVAL_TAC
QED

val _ = export_theory ();
