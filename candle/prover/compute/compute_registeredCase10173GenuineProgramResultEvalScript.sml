(*****************************************************************************
 * Close the source-program result around the memoized genuine case-10173
 * numerical item.
 *
 * The expensive historical item and the ordinary 47-instruction program
 * loop are ancestors of this theory.  This layer evaluates only the small
 * source splice, stack-head, result-conversion, and certified-finish terms.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineProgramResultEval
Ancestors
  compute_registeredCase10173GenuineProgramMemoEval
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_closed_eval_cv_def:
  registered_case10173_closed_eval_cv fuel expression =
    case compute_eval_pure fuel
      registered_case10173_historical_chunk16_ceqs expression of
    | NONE => NONE
    | SOME result => compute_exp_to_cv result
End

Theorem registered_case10173_closed_eval_cv_refines:
  registered_case10173_closed_eval_cv fuel expression = SOME result /\
  fuel <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      expression (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [registered_case10173_closed_eval_cv_def]
  >> every_case_tac
  >> gvs []
  >> drule compute_pureFastTheory.compute_exp_to_cv_sound
  >> strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `fuel`
  >> simp []
QED

Definition registered_case10173_cv_option_default_def:
  registered_case10173_cv_option_default NONE = Num 0 /\
  registered_case10173_cv_option_default (SOME value) = value
End

Theorem registered_case10173_cv_option_default_exact:
  IS_SOME result ==>
  result = SOME (registered_case10173_cv_option_default result)
Proof
  Cases_on `result`
  >> simp [registered_case10173_cv_option_default_def]
QED

Definition registered_case10173_genuine_final_stack_def:
  registered_case10173_genuine_final_stack =
    case
      registered_case10173_hist_program_run_memo 100000
        registered_case10173_genuine_center_boxes
        registered_case10173_first_job_boxes
        registered_case10173_genuine_encoded_radii
        registered_case10173_first_job_roots
        registered_case10173_genuine_hist_item
        registered_case10173_genuine_spliced_center_program
        registered_case10173_genuine_spliced_box_program (Num 0)
    of
    | NONE => Num 0
    | SOME stack => stack
End

Theorem registered_case10173_genuine_program_memo_exact:
  registered_case10173_hist_program_run_memo 100000
      registered_case10173_genuine_center_boxes
      registered_case10173_first_job_boxes
      registered_case10173_genuine_encoded_radii
      registered_case10173_first_job_roots
      registered_case10173_genuine_hist_item
      registered_case10173_genuine_spliced_center_program
      registered_case10173_genuine_spliced_box_program (Num 0) =
    SOME registered_case10173_genuine_final_stack
Proof
  mp_tac
    compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_program_memo_result
  >> strip_tac
  >> simp [registered_case10173_genuine_final_stack_def,AllCaseEqs()]
QED

Theorem registered_case10173_genuine_program_run_eval_exact:
  120098 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots;
         from_cv registered_case10173_genuine_spliced_center_program;
         from_cv registered_case10173_genuine_spliced_box_program;
         from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_final_stack),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_sound
  >> qexists_tac `100000`
  >> qexists_tac `registered_case10173_genuine_hist_item`
  >> qexists_tac `20000`
  >> simp
       [registered_case10173_genuine_program_memo_exact,
        compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_encoded_radii_def,
        compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_hist_item_eval_above_closed,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_program_data_shape]
  >> intLib.ARITH_TAC
QED

val _ = cv_trans registered_case10173_closed_eval_cv_def;
val _ = cv_trans registered_case10173_cv_option_default_def;

val registered_case10173_genuine_center_program_value =
  EVAL ``registered_case10173_genuine_center_program``;
val _ = save_thm
  ("registered_case10173_genuine_center_program_value",
   registered_case10173_genuine_center_program_value);
val _ = cv_trans registered_case10173_genuine_center_program_value;

val registered_case10173_genuine_box_program_value =
  EVAL ``registered_case10173_genuine_box_program``;
val _ = save_thm
  ("registered_case10173_genuine_box_program_value",
   registered_case10173_genuine_box_program_value);
val _ = cv_trans registered_case10173_genuine_box_program_value;

val _ = cv_trans registered_case10173_genuine_final_stack_def;

val registered_case10173_genuine_center_splice_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_case10173_hist_splice_aux»
          [Num 31;from_cv registered_case10173_genuine_center_program]) =
      SOME registered_case10173_genuine_spliced_center_program``;
val _ = save_thm
  ("registered_case10173_genuine_center_splice_exact",
   registered_case10173_genuine_center_splice_exact);

val registered_case10173_genuine_box_splice_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_case10173_hist_splice_aux»
          [Num 31;from_cv registered_case10173_genuine_box_program]) =
      SOME registered_case10173_genuine_spliced_box_program``;
val _ = save_thm
  ("registered_case10173_genuine_box_splice_exact",
   registered_case10173_genuine_box_splice_exact);

Theorem registered_case10173_genuine_center_splice_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_splice_aux»
        [Num 31;from_cv registered_case10173_genuine_center_program])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_spliced_center_program),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_center_splice_exact]
QED

Theorem registered_case10173_genuine_box_splice_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_splice_aux»
        [Num 31;from_cv registered_case10173_genuine_box_program])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_spliced_box_program),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_box_splice_exact]
QED

val registered_case10173_genuine_final_stack_value =
  time cv_eval ``registered_case10173_genuine_final_stack``;
val _ = save_thm
  ("registered_case10173_genuine_final_stack_value",
   registered_case10173_genuine_final_stack_value);
val _ = cv_trans registered_case10173_genuine_final_stack_value;

val registered_case10173_genuine_center_environment_source_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_q_center_environment_list»
          [from_cv registered_case10173_first_job_boxes]) =
      SOME registered_case10173_genuine_center_boxes``;
val _ = save_thm
  ("registered_case10173_genuine_center_environment_source_exact",
   registered_case10173_genuine_center_environment_source_exact);

val registered_case10173_genuine_radius_source_exact =
  time cv_eval
    ``registered_case10173_closed_eval_cv 1000
        (App «candle_cv_q_fixed_list_round_upper»
          [App «candle_cv_q_radius_list»
            [from_cv registered_case10173_first_job_boxes]]) =
      SOME registered_case10173_genuine_encoded_radii``;
val _ = save_thm
  ("registered_case10173_genuine_radius_source_exact",
   registered_case10173_genuine_radius_source_exact);

Definition registered_case10173_genuine_final_item_def:
  registered_case10173_genuine_final_item =
    registered_case10173_cv_option_default
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_fsa_item_head»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_final_stack]))
End

val registered_case10173_genuine_final_item_defined =
  time cv_eval
    ``IS_SOME
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_fsa_item_head»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_final_stack]))``;
val _ = save_thm
  ("registered_case10173_genuine_final_item_defined",
   registered_case10173_genuine_final_item_defined);

Theorem registered_case10173_genuine_final_item_exact:
  registered_case10173_closed_eval_cv 1000
      (App «candle_cv_fsa_item_head»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_final_stack]) =
    SOME registered_case10173_genuine_final_item
Proof
  PURE_REWRITE_TAC [registered_case10173_genuine_final_item_def]
  >> irule registered_case10173_cv_option_default_exact
  >> simp [registered_case10173_genuine_final_item_defined]
QED

val _ = cv_trans registered_case10173_genuine_final_item_def;

Definition registered_case10173_genuine_program_result_def:
  registered_case10173_genuine_program_result =
    registered_case10173_cv_option_default
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_fsa_item_to_q»
          [from_cv registered_case10173_genuine_final_item]))
End

val registered_case10173_genuine_program_result_defined =
  time cv_eval
    ``IS_SOME
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_fsa_item_to_q»
          [from_cv registered_case10173_genuine_final_item]))``;
val _ = save_thm
  ("registered_case10173_genuine_program_result_defined",
   registered_case10173_genuine_program_result_defined);

Theorem registered_case10173_genuine_program_result_exact:
  registered_case10173_closed_eval_cv 1000
      (App «candle_cv_fsa_item_to_q»
        [from_cv registered_case10173_genuine_final_item]) =
    SOME registered_case10173_genuine_program_result
Proof
  PURE_REWRITE_TAC [registered_case10173_genuine_program_result_def]
  >> irule registered_case10173_cv_option_default_exact
  >> simp [registered_case10173_genuine_program_result_defined]
QED

val _ = cv_trans registered_case10173_genuine_program_result_def;

Definition registered_case10173_genuine_certified_verdict_def:
  registered_case10173_genuine_certified_verdict =
    registered_case10173_cv_option_default
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_program_result]))
End

val registered_case10173_genuine_certified_verdict_defined =
  time cv_eval
    ``IS_SOME
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_program_result]))``;
val _ = save_thm
  ("registered_case10173_genuine_certified_verdict_defined",
   registered_case10173_genuine_certified_verdict_defined);

Theorem registered_case10173_genuine_certified_verdict_exact:
  registered_case10173_closed_eval_cv 1000
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_program_result]) =
    SOME registered_case10173_genuine_certified_verdict
Proof
  PURE_REWRITE_TAC [registered_case10173_genuine_certified_verdict_def]
  >> irule registered_case10173_cv_option_default_exact
  >> simp [registered_case10173_genuine_certified_verdict_defined]
QED

val _ = cv_trans registered_case10173_genuine_certified_verdict_def;

Definition registered_case10173_cv_fst_accepts_def:
  registered_case10173_cv_fst_accepts (Num n : cv) = F /\
  registered_case10173_cv_fst_accepts (Pair first detail) =
    (first = Num 1)
End

Theorem registered_case10173_cv_fst_accepts_shape:
  registered_case10173_cv_fst_accepts verdict ==>
  ?detail. verdict = Pair (Num 1) detail
Proof
  Cases_on `verdict`
  >> simp [registered_case10173_cv_fst_accepts_def]
QED

val _ = cv_trans registered_case10173_cv_fst_accepts_def;

val registered_case10173_genuine_certified_verdict_accepts =
  time cv_eval
    ``registered_case10173_cv_fst_accepts
        registered_case10173_genuine_certified_verdict``;
val _ = save_thm
  ("registered_case10173_genuine_certified_verdict_accepts",
   registered_case10173_genuine_certified_verdict_accepts);

Theorem registered_case10173_genuine_center_environment_source_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list»
        [from_cv registered_case10173_first_job_boxes])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_center_boxes),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_center_environment_source_exact]
QED

Theorem registered_case10173_genuine_radius_source_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list»
          [from_cv registered_case10173_first_job_boxes]])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_encoded_radii),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_radius_source_exact]
QED

Theorem registered_case10173_genuine_final_item_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_head»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_final_stack])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_final_item),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_final_item_exact]
QED

Theorem registered_case10173_genuine_program_result_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q»
        [from_cv registered_case10173_genuine_final_item])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_program_result),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_program_result_exact]
QED

Theorem registered_case10173_genuine_certified_finish_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_program_result])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_certified_verdict),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_certified_verdict_exact]
QED

Theorem registered_case10173_genuine_program_run_spliced_eval:
  120098 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots;
         App «candle_cv_case10173_hist_splice_aux»
           [Num 31;from_cv registered_case10173_genuine_center_program];
         App «candle_cv_case10173_hist_splice_aux»
           [Num 31;from_cv registered_case10173_genuine_box_program];
         Num 0])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_final_stack),refs)
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_encoded_radii;
           from_cv registered_case10173_first_job_roots;
           App «candle_cv_case10173_hist_splice_aux»
             [Num 31;from_cv registered_case10173_genuine_center_program];
           App «candle_cv_case10173_hist_splice_aux»
             [Num 31;from_cv registered_case10173_genuine_box_program];
           Num 0]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv registered_case10173_genuine_center_boxes;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_genuine_encoded_radii;
           from_cv registered_case10173_first_job_roots;
           from_cv registered_case10173_genuine_spliced_center_program;
           from_cv registered_case10173_genuine_spliced_box_program;
           from_cv (Num 0)]) refs` by
       (irule
          compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_app7_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              registered_case10173_genuine_center_splice_eval,
              registered_case10173_genuine_box_splice_eval,
              compute_evalTheory.compute_eval_def,
              ml_monadBaseTheory.st_ex_return_def]
        >> intLib.ARITH_TAC)
  >> pop_assum SUBST1_TAC
  >> simp [registered_case10173_genuine_program_run_eval_exact]
QED

Theorem registered_case10173_genuine_hist_program_eval:
  120102 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv registered_case10173_genuine_center_program;
         from_cv registered_case10173_genuine_box_program;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_program_result),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramEvalTheory.registered_case10173_hist_program_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `registered_case10173_genuine_center_boxes`
  >> qexists_tac `registered_case10173_genuine_final_item`
  >> qexists_tac `registered_case10173_genuine_encoded_radii`
  >> qexists_tac `registered_case10173_genuine_final_stack`
  >> conj_tac
  >- (irule registered_case10173_genuine_center_environment_source_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule registered_case10173_genuine_program_run_spliced_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule registered_case10173_genuine_final_item_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule registered_case10173_genuine_program_result_eval
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_genuine_radius_source_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_genuine_hist_certified_check_eval:
  120103 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_certified_check»
        [from_cv registered_case10173_genuine_center_program;
         from_cv registered_case10173_genuine_box_program;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_genuine_certified_verdict),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_hist_certified_check_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `registered_case10173_genuine_program_result`
  >> conj_tac
  >- (irule registered_case10173_genuine_hist_program_eval
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_genuine_certified_finish_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_genuine_hist_certified_check_accept:
  120103 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Uop Fst
        (App «candle_cv_case10173_hist_certified_check»
          [from_cv registered_case10173_genuine_center_program;
           from_cv registered_case10173_genuine_box_program;
           from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_first_job_roots]))
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`verdict` |-> `registered_case10173_genuine_certified_verdict`]
         registered_case10173_cv_fst_accepts_shape)
  >> impl_tac
  >- simp [registered_case10173_genuine_certified_verdict_accepts]
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_genuine_hist_certified_check_eval,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
