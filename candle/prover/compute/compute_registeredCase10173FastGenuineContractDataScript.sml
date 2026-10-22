(*****************************************************************************
 * Stable authenticated source contract for the genuine first NL job.
 *
 * This is kept below the changing evaluator composition layer so its closed
 * arithmetic check is retained across later wrapper and theorem-handoff
 * edits.
 *****************************************************************************)
Theory compute_registeredCase10173FastGenuineContractData
Ancestors
  compute_registeredCase10173SourceAlignedLiteralData
  compute_registeredCase10173GenuineProgramData
Libs
  bossLib preamble wordsLib cv_transLib

Definition registered_case10173_first_job_object_job_def:
  registered_case10173_first_job_object_job =
    case bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp of
    | SOME (Pair object_job root_record) => object_job
    | NONE => Num 0
End

Theorem registered_case10173_first_job_object_job_exact:
  bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
    SOME
      (Pair registered_case10173_first_job_object_job
        registered_case10173_first_job_roots)
Proof
  simp
    [registered_case10173_first_job_object_job_def,
     compute_registeredCase10173RootRecordValueTheory.registered_case10173_first_job_roots_def,
     compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def]
QED

Theorem registered_case10173_first_job_source_actual_sqrt_contract:
  bounded_case10173_source_actual_sqrt_contract
    bounded_case10173_decimal_packet0_source_aligned
    registered_case10173_first_job_object_job
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

val registered_case10173_first_job_object_job_value =
  EVAL ``registered_case10173_first_job_object_job``;
val _ = save_thm
  ("registered_case10173_first_job_object_job_value",
   registered_case10173_first_job_object_job_value);
val _ = cv_trans registered_case10173_first_job_object_job_value;

val _ = export_theory ();
