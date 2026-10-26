(*****************************************************************************
 * Exact memoized program evaluation for the first genuine case-10173 job in
 * the corrected tag-10 environment.  Reuse the authenticated inputs and the
 * proved historical item; only the private splice marker changes.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10GenuineProgramMemoEval
Ancestors
  compute_registeredCase10173Tag10HistProgramMemoEval
  compute_registeredCase10173Tag10EnvironmentCV
  compute_registeredCase10173GenuineProgramMemoEval
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_tag10_hist_splice_cv_def:
  registered_case10173_tag10_hist_splice_cv 0 program =
    Pair (Num 10) (registered_case10173_cv_drop 8 program) /\
  registered_case10173_tag10_hist_splice_cv (SUC count)
      (Pair instruction program) =
    Pair instruction
      (registered_case10173_tag10_hist_splice_cv count program) /\
  registered_case10173_tag10_hist_splice_cv (SUC count) (Num n) = Num n
End

Definition registered_case10173_tag10_spliced_box_program_def:
  registered_case10173_tag10_spliced_box_program =
    registered_case10173_tag10_hist_splice_cv 31
      registered_case10173_genuine_box_program
End

Definition registered_case10173_tag10_spliced_center_program_def:
  registered_case10173_tag10_spliced_center_program =
    registered_case10173_tag10_hist_splice_cv 31
      registered_case10173_genuine_center_program
End

Theorem registered_case10173_tag10_hist_splice_length:
  !count program.
    registered_case10173_cv_list_length
      (registered_case10173_tag10_hist_splice_cv count program) =
    registered_case10173_cv_list_length
      (registered_case10173_hist_splice_cv count program)
Proof
  Induct
  >> Cases
  >> simp
       [registered_case10173_tag10_hist_splice_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_hist_splice_cv_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem registered_case10173_tag10_program_data_shape:
  registered_case10173_cv_list_length
      registered_case10173_tag10_spliced_box_program = 47 /\
  registered_case10173_cv_list_length
      registered_case10173_tag10_spliced_center_program = 47
Proof
  simp
    [registered_case10173_tag10_spliced_box_program_def,
     registered_case10173_tag10_spliced_center_program_def,
     registered_case10173_tag10_hist_splice_length]
  >> mp_tac
       compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_program_data_shape
  >> simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_spliced_box_program_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_spliced_center_program_def]
QED

Theorem registered_case10173_tag10_genuine_hist_item_eval_above_closed:
  compute_registeredCase10173Tag10HistProgramMemoEval$registered_case10173_hist_item_eval_above
    20000 registered_case10173_genuine_center_boxes
    registered_case10173_first_job_boxes
    (registered_case10173_q_cv_list
      registered_case10173_historical_encoded_radii)
    registered_case10173_first_job_roots
    registered_case10173_genuine_hist_item
Proof
  mp_tac
    compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_hist_item_eval_above_closed
  >> simp
       [compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_item_eval_above_def,
        compute_registeredCase10173Tag10HistProgramMemoEvalTheory.registered_case10173_hist_item_eval_above_def,
        compute_registeredCase10173Tag10HistItemCongruenceTheory.registered_case10173_hist_item_old_tag10_eval_cong]
QED

val registered_case10173_tag10_hist_program_run_memo_pre_def =
  cv_auto_trans_pre ""
    (compute_registeredCase10173Tag10HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_def
      |> measure_args [6]);

Theorem registered_case10173_tag10_hist_program_run_memo_pre[cv_pre]:
  !fuel center_boxes boxes radii roots item center_program box_program stack.
    registered_case10173_hist_program_run_memo_pre' fuel
      center_boxes boxes radii roots item center_program box_program stack
Proof
  Induct_on `center_program`
  >- rw [Once registered_case10173_tag10_hist_program_run_memo_pre_def]
  >> rpt gen_tac
  >> Cases_on `box_program`
  >> rw [Once registered_case10173_tag10_hist_program_run_memo_pre_def]
  >> every_case_tac
  >> gvs []
QED

val registered_case10173_tag10_spliced_center_program_value =
  EVAL ``registered_case10173_tag10_spliced_center_program``;
val _ = save_thm
  ("registered_case10173_tag10_spliced_center_program_value",
   registered_case10173_tag10_spliced_center_program_value);
val _ = cv_trans registered_case10173_tag10_spliced_center_program_value;

val registered_case10173_tag10_spliced_box_program_value =
  EVAL ``registered_case10173_tag10_spliced_box_program``;
val _ = save_thm
  ("registered_case10173_tag10_spliced_box_program_value",
   registered_case10173_tag10_spliced_box_program_value);
val _ = cv_trans registered_case10173_tag10_spliced_box_program_value;

val registered_case10173_tag10_genuine_program_memo_defined =
  time cv_eval
    ``IS_SOME
      (compute_registeredCase10173Tag10HistProgramMemoEval$registered_case10173_hist_program_run_memo
        100000 registered_case10173_genuine_center_boxes
        registered_case10173_first_job_boxes
        registered_case10173_genuine_encoded_radii
        registered_case10173_first_job_roots
        registered_case10173_genuine_hist_item
        registered_case10173_tag10_spliced_center_program
        registered_case10173_tag10_spliced_box_program (Num 0))``;

val _ = save_thm
  ("registered_case10173_tag10_genuine_program_memo_defined",
   registered_case10173_tag10_genuine_program_memo_defined);

Theorem registered_case10173_tag10_genuine_program_memo_result:
  ?final_stack.
    compute_registeredCase10173Tag10HistProgramMemoEval$registered_case10173_hist_program_run_memo
      100000 registered_case10173_genuine_center_boxes
      registered_case10173_first_job_boxes
      registered_case10173_genuine_encoded_radii
      registered_case10173_first_job_roots
      registered_case10173_genuine_hist_item
      registered_case10173_tag10_spliced_center_program
      registered_case10173_tag10_spliced_box_program (Num 0) =
    SOME final_stack
Proof
  mp_tac registered_case10173_tag10_genuine_program_memo_defined
  >> simp [IS_SOME_EXISTS]
QED

Theorem registered_case10173_tag10_genuine_program_run_eval:
  120098 < clock ==>
  ?final_stack.
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots;
         from_cv registered_case10173_tag10_spliced_center_program;
         from_cv registered_case10173_tag10_spliced_box_program;
         from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv final_stack),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_tag10_genuine_program_memo_result
  >> strip_tac
  >> qexists_tac `final_stack`
  >> irule
       compute_registeredCase10173Tag10HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_sound
  >> qexists_tac `100000`
  >> qexists_tac `registered_case10173_genuine_hist_item`
  >> qexists_tac `20000`
  >> simp
       [registered_case10173_tag10_genuine_program_memo_result,
        compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_encoded_radii_def,
        registered_case10173_tag10_genuine_hist_item_eval_above_closed,
        registered_case10173_tag10_program_data_shape]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
