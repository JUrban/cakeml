(*****************************************************************************
 * Lift the first genuine historical item through the registered opcode-9
 * dispatch and the corresponding one-instruction program loop.  Keeping this
 * layer separate lets the exact source-program proof reuse the completed
 * numerical item without reopening its center/box calculation.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineHistStepEval
Ancestors
  compute_registeredCase10173GenuineHistItemCallEval
Libs
  bossLib preamble

Theorem registered_case10173_genuine_historical_special_step_eval:
  20001 < clock ==>
  ?center_boxes result.
    registered_case10173_q_center_environment_positive
        registered_case10173_first_job_boxes = SOME center_boxes /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_step»
        [from_cv center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv
           (registered_case10173_q_cv_list
             registered_case10173_historical_encoded_radii);
         from_cv registered_case10173_first_job_roots;
         from_cv (Num 9);from_cv (Num 9);from_cv stack])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Pair (Num 1) result) stack)),refs)
Proof
  strip_tac
  >> `0 < clock` by intLib.ARITH_TAC
  >> mp_tac
       (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
         compute_registeredCase10173GenuineHistItemCallEvalTheory.registered_case10173_genuine_historical_item_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> metis_tac
       [compute_registeredCase10173HistStepEvalTheory.registered_case10173_hist_step_special_eval_from_item]
QED

Theorem registered_case10173_genuine_historical_singleton_run_eval:
  20002 < clock ==>
  ?center_boxes result.
    registered_case10173_q_center_environment_positive
        registered_case10173_first_job_boxes = SOME center_boxes /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv
           (registered_case10173_q_cv_list
             registered_case10173_historical_encoded_radii);
         from_cv registered_case10173_first_job_roots;
         from_cv (Pair (Num 9) (Num 0));
         from_cv (Pair (Num 9) (Num 0));
         from_cv stack])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Pair (Num 1) result) stack)),refs)
Proof
  strip_tac
  >> `1 < clock /\ 0 < clock - 1` by intLib.ARITH_TAC
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`, `refs` |-> `refs`, `stack` |-> `stack`]
         registered_case10173_genuine_historical_special_step_eval)
  >> impl_tac >- intLib.ARITH_TAC
  >> strip_tac
  >> metis_tac
       [compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_cons_eval,
        compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_center_nil_eval]
QED

val _ = export_theory ();
