(*****************************************************************************
 * Closed proof-producing production-guard result for the genuine first job.
 *
 * The expensive registered equation-table translation is inherited from the
 * root-record milestone.  This theory therefore isolates the recurring cost
 * of the literal historical guard on the same authenticated boxes and roots.
 *****************************************************************************)
Theory compute_registeredCase10173ProductionGuardValue
Ancestors
  compute_registeredCase10173RootRecordValue
Libs
  bossLib preamble cv_transLib

val registered_case10173_first_production_guard_pure_eval =
  time cv_eval
    ``compute_eval_pure 100000
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_production_guard»
          [from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_first_job_roots])``;

val _ = save_thm
  ("registered_case10173_first_production_guard_pure_eval",
   registered_case10173_first_production_guard_pure_eval);

Theorem registered_case10173_first_production_guard_pure_eval_value:
  compute_eval_pure 100000 registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots]) =
    SOME (Num 1)
Proof
  simp [registered_case10173_first_production_guard_pure_eval,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
