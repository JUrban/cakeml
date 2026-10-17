(*****************************************************************************
 * Registered evaluator control seam for the historical numerical program.
 *
 * The expensive instruction execution is deliberately left as one explicit
 * [hist_program_run] result.  This theory proves all surrounding source
 * control: center/radius preparation, stack-head selection, item conversion,
 * and the two let bindings.  The packed object refinement can therefore
 * target the program-run result without replaying the complete wrapper.
 *****************************************************************************)
Theory compute_registeredCase10173HistProgramEval
Ancestors
  compute_registeredCase10173CertifiedFinishEval
Libs
  bossLib preamble

Definition registered_case10173_hist_program_body_def:
  registered_case10173_hist_program_body =
    Let «center_boxes»
      (App «candle_cv_q_center_environment_list» [Var «boxes»])
      (Let «radii»
        (App «candle_cv_q_fixed_list_round_upper»
          [App «candle_cv_q_radius_list» [Var «boxes»]])
        (App «candle_cv_fsa_item_to_q»
          [App «candle_cv_fsa_item_head»
            [Var «center_boxes»;Var «boxes»;
             App «candle_cv_case10173_hist_program_run»
               [Var «center_boxes»;Var «boxes»;Var «radii»;
                Var «roots»;
                App «candle_cv_case10173_hist_splice_aux»
                  [Num 31;Var «center_program»];
                App «candle_cv_case10173_hist_splice_aux»
                  [Num 31;Var «box_program»];
                Num 0]]]))
End

Theorem registered_case10173_hist_program_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_program» =
    SOME
      ([«center_program»;«box_program»;«boxes»;«roots»],
       registered_case10173_hist_program_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_program_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_program»,from_cv center_program);
         («box_program»,from_cv box_program);
         («boxes»,from_cv boxes);(«roots»,from_cv roots)]
        registered_case10173_hist_program_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_hist_program_lookup]
QED

Theorem registered_case10173_hist_program_eval_from_results:
  3 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list» [from_cv boxes])
      (refs:hol_refs) =
      (M_success (from_cv center_boxes),refs) /\
  compute_eval (clock - 2)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) refs =
      (M_success (from_cv radii),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         App «candle_cv_case10173_hist_splice_aux»
           [Num 31;from_cv center_program];
         App «candle_cv_case10173_hist_splice_aux»
           [Num 31;from_cv box_program];
         Num 0]) refs =
      (M_success (from_cv stack),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_head»
        [from_cv center_boxes;from_cv boxes;from_cv stack]) refs =
      (M_success (from_cv item),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q» [from_cv item]) refs =
      (M_success (from_cv program_result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) refs =
    (M_success (from_cv program_result),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_program_unfold]
  >> simp
       [registered_case10173_hist_program_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv center_boxes`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv radii`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> `compute_eval (clock - 3)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_head»
          [from_cv center_boxes;from_cv boxes;
           App «candle_cv_case10173_hist_program_run»
             [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
              App «candle_cv_case10173_hist_splice_aux»
                [Num 31;from_cv center_program];
              App «candle_cv_case10173_hist_splice_aux»
                [Num 31;from_cv box_program];
              Num 0]]) refs =
      compute_eval (clock - 3)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_head»
          [from_cv center_boxes;from_cv boxes;from_cv stack]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
        >> fs [compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 3)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_to_q»
          [App «candle_cv_fsa_item_head»
            [from_cv center_boxes;from_cv boxes;
             App «candle_cv_case10173_hist_program_run»
               [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
                App «candle_cv_case10173_hist_splice_aux»
                  [Num 31;from_cv center_program];
                App «candle_cv_case10173_hist_splice_aux»
                  [Num 31;from_cv box_program];
                Num 0]]]) refs =
      compute_eval (clock - 3)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsa_item_to_q» [from_cv item]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> fs [])
  >> fs []
QED

val _ = export_theory ();
