(*****************************************************************************
 * Exact three-definition delta between the historical tag-9 and corrected
 * tag-10 generated equation environments.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10EnvironmentDelta
Ancestors
  compute_registeredCase10173HistoricalChunk16Data
  compute_registeredCase10173HistoricalChunk16Tag10Data
Libs
  bossLib preamble

Definition registered_case10173_tag10_environment_from_old_def:
  registered_case10173_tag10_environment_from_old =
    AFUPDKEY «candle_cv_case10173_hist_step»
      (K (THE (ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
        «candle_cv_case10173_hist_step»)))
      (AFUPDKEY «candle_cv_case10173_hist_splice_aux»
        (K (THE (ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
          «candle_cv_case10173_hist_splice_aux»)))
        (AFUPDKEY «candle_cv_fso_program_step_fixed_nonlinear»
          (K (THE (ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
            «candle_cv_fso_program_step_fixed_nonlinear»)))
          registered_case10173_historical_chunk16_ceqs))
End

Theorem registered_case10173_tag10_environment_exact_delta:
  registered_case10173_historical_chunk16_tag10_ceqs =
    registered_case10173_tag10_environment_from_old
Proof
  EVAL_TAC
QED

Theorem ALOOKUP_AFUPDKEY_other:
  lookup_key <> updated_key ==>
  ALOOKUP (AFUPDKEY updated_key replacement ceqs) lookup_key =
    ALOOKUP ceqs lookup_key
Proof
  strip_tac
  >> rw [AFUPDKEY_ALOOKUP]
  >> Cases_on `ALOOKUP ceqs lookup_key`
  >> simp []
QED

Theorem ALOOKUP_three_AFUPDKEY_other:
  lookup_key <> key1 /\ lookup_key <> key2 /\ lookup_key <> key3 ==>
  ALOOKUP
    (AFUPDKEY key3 replacement3
      (AFUPDKEY key2 replacement2
        (AFUPDKEY key1 replacement1 ceqs)))
    lookup_key = ALOOKUP ceqs lookup_key
Proof
  strip_tac
  >> `ALOOKUP
        (AFUPDKEY key3 replacement3
          (AFUPDKEY key2 replacement2
            (AFUPDKEY key1 replacement1 ceqs)))
        lookup_key =
      ALOOKUP
        (AFUPDKEY key2 replacement2
          (AFUPDKEY key1 replacement1 ceqs))
        lookup_key` by metis_tac [ALOOKUP_AFUPDKEY_other]
  >> `ALOOKUP
        (AFUPDKEY key2 replacement2
          (AFUPDKEY key1 replacement1 ceqs))
        lookup_key =
      ALOOKUP (AFUPDKEY key1 replacement1 ceqs) lookup_key` by
    metis_tac [ALOOKUP_AFUPDKEY_other]
  >> `ALOOKUP (AFUPDKEY key1 replacement1 ceqs) lookup_key =
      ALOOKUP ceqs lookup_key` by
    metis_tac [ALOOKUP_AFUPDKEY_other]
  >> metis_tac []
QED

Theorem registered_case10173_tag10_lookup_unchanged:
  function_name <> «candle_cv_fso_program_step_fixed_nonlinear» /\
  function_name <> «candle_cv_case10173_hist_splice_aux» /\
  function_name <> «candle_cv_case10173_hist_step» ==>
  ALOOKUP registered_case10173_historical_chunk16_ceqs function_name =
    ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs function_name
Proof
  strip_tac
  >> once_rewrite_tac [registered_case10173_tag10_environment_exact_delta]
  >> once_rewrite_tac [registered_case10173_tag10_environment_from_old_def]
  >> metis_tac [ALOOKUP_three_AFUPDKEY_other]
QED

val _ = export_theory ();
