(*****************************************************************************
 * Closed proof-producing probe for the genuine first historical root record.
 *
 * This is deliberately a milestone probe, not the scalable batch bridge: it
 * evaluates the literal source check on the boxes and roots extracted from
 * the authenticated first object job.  The generic interval-algebra proof
 * remains necessary before this result can be amortized over all cells.
 *****************************************************************************)
Theory compute_registeredCase10173RootRecordValue
Ancestors
  compute_evalPure
  compute_registeredCase10173RootInputsBinding
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_first_job_boxes_def:
  registered_case10173_first_job_boxes =
    case bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp of
    | SOME
        (Pair
          (Pair box_sqrt_data (Pair center_sqrt_data boxes))
          root_record) => boxes
    | _ => Num 0
End

Definition registered_case10173_first_job_roots_def:
  registered_case10173_first_job_roots =
    case bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp of
    | SOME (Pair object_job root_record) => root_record
    | _ => Num 0
End

val compute_exp_to_cv_pre_def =
  cv_trans_pre "" compute_pureFastTheory.compute_exp_to_cv_def;

Theorem compute_exp_to_cv_pre[cv_pre]:
  !expression. compute_exp_to_cv_pre expression
Proof
  ho_match_mp_tac compute_pureFastTheory.compute_exp_to_cv_ind
  >> rw []
  >> simp [Once compute_exp_to_cv_pre_def]
QED

val _ = cv_trans
  compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def;
val _ = cv_trans
  compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def;
val _ = cv_trans registered_case10173_first_job_boxes_def;
val _ = cv_trans registered_case10173_first_job_roots_def;
val _ = cv_trans compute_execTheory.from_cv_def;
val _ = cv_trans
  compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_ceqs_def;

val registered_case10173_first_root_record_pure_eval =
  time cv_eval
    ``compute_eval_pure 100000
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_root_record_check»
          [from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_first_job_roots])``;

val _ = save_thm
  ("registered_case10173_first_root_record_pure_eval",
   registered_case10173_first_root_record_pure_eval);

Theorem registered_case10173_first_root_record_pure_eval_value:
  compute_eval_pure 100000 registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_root_record_check»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots]) =
    SOME (Num 1)
Proof
  simp [registered_case10173_first_root_record_pure_eval,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
