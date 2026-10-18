(*****************************************************************************
 * Discharge the complete registered checked-job head contract for the first
 * authenticated genuine case-10173 job.
 *
 * The numerical certified acceptance is inherited.  This theory adds the
 * actual root/guard and square-root program-preparation checks which surround
 * it in the production checked-job stream.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineCheckedHeadEval
Ancestors
  compute_registeredCase10173GenuineProgramResultEval
Libs
  bossLib preamble cv_transLib

val registered_case10173_genuine_source_program_value =
  EVAL ``registered_case10173_genuine_source_program``;
val _ = save_thm
  ("registered_case10173_genuine_source_program_value",
   registered_case10173_genuine_source_program_value);
val _ = cv_trans registered_case10173_genuine_source_program_value;

val registered_case10173_first_job_box_sqrt_data_value =
  EVAL ``registered_case10173_first_job_box_sqrt_data``;
val _ = save_thm
  ("registered_case10173_first_job_box_sqrt_data_value",
   registered_case10173_first_job_box_sqrt_data_value);
val _ = cv_trans registered_case10173_first_job_box_sqrt_data_value;

val registered_case10173_first_job_center_sqrt_data_value =
  EVAL ``registered_case10173_first_job_center_sqrt_data``;
val _ = save_thm
  ("registered_case10173_first_job_center_sqrt_data_value",
   registered_case10173_first_job_center_sqrt_data_value);
val _ = cv_trans registered_case10173_first_job_center_sqrt_data_value;

val registered_case10173_genuine_box_sqrt_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv registered_case10173_first_job_box_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) =
      SOME (Num 1)``;
val _ = save_thm
  ("registered_case10173_genuine_box_sqrt_exact",
   registered_case10173_genuine_box_sqrt_exact);

val registered_case10173_genuine_box_patch_source_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_analytic_program_patch_sqrt»
          [from_cv registered_case10173_first_job_box_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) =
      SOME
        (Pair (Num 0) registered_case10173_genuine_box_program)``;
val _ = save_thm
  ("registered_case10173_genuine_box_patch_source_exact",
   registered_case10173_genuine_box_patch_source_exact);

val registered_case10173_genuine_center_sqrt_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv registered_case10173_first_job_center_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) =
      SOME (Num 1)``;
val _ = save_thm
  ("registered_case10173_genuine_center_sqrt_exact",
   registered_case10173_genuine_center_sqrt_exact);

val registered_case10173_genuine_center_patch_source_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_analytic_program_patch_sqrt»
          [from_cv registered_case10173_first_job_center_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) =
      SOME
        (Pair (Num 0) registered_case10173_genuine_center_program)``;
val _ = save_thm
  ("registered_case10173_genuine_center_patch_source_exact",
   registered_case10173_genuine_center_patch_source_exact);

Theorem registered_case10173_first_root_record_eval:
  100000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_root_record_check»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `100000`
  >> simp
       [compute_registeredCase10173RootRecordValueTheory.registered_case10173_first_root_record_pure_eval_value]
QED

Theorem registered_case10173_first_production_guard_eval:
  100000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `100000`
  >> simp
       [compute_registeredCase10173ProductionGuardValueTheory.registered_case10173_first_production_guard_pure_eval_value]
QED

Theorem registered_case10173_genuine_box_sqrt_data_exact_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_sqrt_data_exact»
        [from_cv registered_case10173_first_job_box_sqrt_data;
         from_cv registered_case10173_genuine_source_program])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`fuel` |-> `1000`,
          `expression` |->
            `App «candle_cv_analytic_program_sqrt_data_exact»
              [from_cv registered_case10173_first_job_box_sqrt_data;
               from_cv registered_case10173_genuine_source_program]`,
          `result` |-> `Num 1`, `clock` |-> `clock`, `refs` |-> `refs`]
         compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_closed_eval_cv_refines)
  >> simp
       [registered_case10173_genuine_box_sqrt_exact,
        compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_genuine_box_patch_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_patch_sqrt»
        [from_cv registered_case10173_first_job_box_sqrt_data;
         from_cv registered_case10173_genuine_source_program])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 0) registered_case10173_genuine_box_program)),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_closed_eval_cv_refines)
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_box_patch_source_exact]
QED

Theorem registered_case10173_genuine_center_sqrt_data_exact_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_sqrt_data_exact»
        [from_cv registered_case10173_first_job_center_sqrt_data;
         from_cv registered_case10173_genuine_source_program])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`fuel` |-> `1000`,
          `expression` |->
            `App «candle_cv_analytic_program_sqrt_data_exact»
              [from_cv registered_case10173_first_job_center_sqrt_data;
               from_cv registered_case10173_genuine_source_program]`,
          `result` |-> `Num 1`, `clock` |-> `clock`, `refs` |-> `refs`]
         compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_closed_eval_cv_refines)
  >> simp
       [registered_case10173_genuine_center_sqrt_exact,
        compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_genuine_center_patch_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_analytic_program_patch_sqrt»
        [from_cv registered_case10173_first_job_center_sqrt_data;
         from_cv registered_case10173_genuine_source_program])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 0) registered_case10173_genuine_center_program)),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_center_patch_source_exact]
QED

Theorem registered_case10173_genuine_checked_job_head_eval_ok:
  120105 < clock ==>
  registered_case10173_hist_checked_job_head_eval_ok clock
    registered_case10173_genuine_source_program
    registered_case10173_first_job_box_sqrt_data
    registered_case10173_first_job_center_sqrt_data
    registered_case10173_first_job_boxes
    registered_case10173_first_job_roots
    (Num 0) registered_case10173_genuine_box_program
    (Num 0) registered_case10173_genuine_center_program refs
Proof
  strip_tac
  >> rw
       [compute_registeredCase10173CheckedJobsEvalTheory.registered_case10173_hist_checked_job_head_eval_ok_def]
  >> FIRST
       [irule registered_case10173_first_root_record_eval,
        irule registered_case10173_first_production_guard_eval,
        irule registered_case10173_genuine_box_sqrt_data_exact_eval,
        irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            registered_case10173_genuine_box_patch_eval),
        irule registered_case10173_genuine_center_sqrt_data_exact_eval,
        irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            registered_case10173_genuine_center_patch_eval),
        irule
          compute_registeredCase10173GenuineProgramResultEvalTheory.registered_case10173_genuine_hist_certified_check_accept]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
