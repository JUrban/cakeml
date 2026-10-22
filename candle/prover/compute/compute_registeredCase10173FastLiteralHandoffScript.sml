(*****************************************************************************
 * Small theorem handoff for the fast literal case-10173 result.
 *
 * The numerical authority here is the source-aligned literal checker.  The
 * earlier genuine-program theory is imported only for its generic closed
 * evaluator refinement and option helper; none of its memoized program-run
 * result, final stack, item, or verdict theorems is used below.
 *****************************************************************************)
Theory compute_registeredCase10173FastLiteralHandoff
Ancestors
  compute_registeredCase10173GenuineProgramResultEval
  compute_registeredCase10173FastLiteralResultData
  compute_registeredCase10173LiteralAddChainEval
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_fast_literal_item_def:
  registered_case10173_fast_literal_item =
    Pair (Num 1)
      (registered_case10173_taylor_object
        registered_case10173_fast_literal_result)
End

val registered_case10173_fast_literal_item_value =
  time
    (REWRITE_CONV
       [registered_case10173_fast_literal_item_def,
        compute_registeredCase10173FastLiteralResultDataTheory.registered_case10173_fast_literal_result_value]
     THENC EVAL)
    ``registered_case10173_fast_literal_item``;
val _ = save_thm
  ("registered_case10173_fast_literal_item_value",
   registered_case10173_fast_literal_item_value);
val _ = cv_trans registered_case10173_fast_literal_item_value;

Definition registered_case10173_fast_program_result_def:
  registered_case10173_fast_program_result =
    registered_case10173_cv_option_default
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_fsa_item_to_q»
          [from_cv registered_case10173_fast_literal_item]))
End

val registered_case10173_fast_program_result_defined =
  time cv_eval
    ``IS_SOME
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_fsa_item_to_q»
          [from_cv registered_case10173_fast_literal_item]))``;
val _ = save_thm
  ("registered_case10173_fast_program_result_defined",
   registered_case10173_fast_program_result_defined);

Theorem registered_case10173_fast_program_result_exact:
  registered_case10173_closed_eval_cv 1000
      (App «candle_cv_fsa_item_to_q»
        [from_cv registered_case10173_fast_literal_item]) =
    SOME registered_case10173_fast_program_result
Proof
  PURE_REWRITE_TAC [registered_case10173_fast_program_result_def]
  >> irule registered_case10173_cv_option_default_exact
  >> simp [registered_case10173_fast_program_result_defined]
QED

val _ = cv_trans registered_case10173_fast_program_result_def;

Definition registered_case10173_fast_certified_verdict_def:
  registered_case10173_fast_certified_verdict =
    registered_case10173_cv_option_default
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_fast_program_result]))
End

val registered_case10173_fast_certified_verdict_defined =
  time cv_eval
    ``IS_SOME
      (registered_case10173_closed_eval_cv 1000
        (App «candle_cv_q_dim_taylor_model_certified_finish»
          [from_cv registered_case10173_first_job_boxes;
           from_cv registered_case10173_fast_program_result]))``;
val _ = save_thm
  ("registered_case10173_fast_certified_verdict_defined",
   registered_case10173_fast_certified_verdict_defined);

Theorem registered_case10173_fast_certified_verdict_exact:
  registered_case10173_closed_eval_cv 1000
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_fast_program_result]) =
    SOME registered_case10173_fast_certified_verdict
Proof
  PURE_REWRITE_TAC [registered_case10173_fast_certified_verdict_def]
  >> irule registered_case10173_cv_option_default_exact
  >> simp [registered_case10173_fast_certified_verdict_defined]
QED

val _ = cv_trans registered_case10173_fast_certified_verdict_def;

val registered_case10173_fast_certified_verdict_accepts =
  time cv_eval
    ``registered_case10173_cv_fst_accepts
        registered_case10173_fast_certified_verdict``;
val _ = save_thm
  ("registered_case10173_fast_certified_verdict_accepts",
   registered_case10173_fast_certified_verdict_accepts);

Theorem registered_case10173_fast_program_result_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q»
        [from_cv registered_case10173_fast_literal_item])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_fast_program_result),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_fast_program_result_exact]
QED

Theorem registered_case10173_fast_certified_finish_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_dim_taylor_model_certified_finish»
        [from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_fast_program_result])
      (refs:hol_refs) =
    (M_success
      (from_cv registered_case10173_fast_certified_verdict),refs)
Proof
  strip_tac
  >> irule registered_case10173_closed_eval_cv_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_fast_certified_verdict_exact]
QED

val _ = export_theory ();
