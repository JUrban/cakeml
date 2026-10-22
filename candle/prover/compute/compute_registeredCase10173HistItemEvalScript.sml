(*****************************************************************************
 * Registered evaluator control seam for the historical dihedral item.
 * Environment conversion, first order, second order, and final completion
 * remain separate results so the existing object-refinement ledger can be
 * connected without replaying the large source evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173HistItemEval
Ancestors
  compute_registeredCase10173HistStepEval
Libs
  bossLib preamble

Definition registered_case10173_hist_item_body_def:
  registered_case10173_hist_item_body =
    Let «center_environment»
      (App «candle_cv_fs_interval_list_of_q» [Var «center_boxes»])
      (Let «box_environment»
        (App «candle_cv_fs_interval_list_of_q» [Var «boxes»])
        (Let «center_first»
          (App «candle_cv_fs_hist_first_order»
            [Var «center_environment»;
             App «candle_cv_fs_interval_lookup» [Num 0;Var «roots»];
             App «candle_cv_fs_interval_lookup» [Num 1;Var «roots»]])
          (Let «box_second»
            (App «candle_cv_fs_hist_second_order»
              [Var «box_environment»;
               App «candle_cv_fs_interval_lookup» [Num 2;Var «roots»];
               App «candle_cv_fs_interval_lookup» [Num 3;Var «roots»]])
            (App «candle_cv_fsa_item_fixed»
              [App «candle_cv_fs_result_complete_rounded»
                [App «candle_cv_fs_list_of_q» [Var «radii»];Num 1;
                 Var «center_first»;
                 App «candle_cv_fs_hist_second_hessian»
                   [Var «box_second»]]]))))
End

Theorem registered_case10173_hist_item_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_case10173_hist_item» =
    SOME
      ([«center_boxes»;«boxes»;«radii»;«roots»],
       registered_case10173_hist_item_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_item_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);(«roots»,from_cv roots)]
        registered_case10173_hist_item_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_hist_item_lookup]
QED

Theorem registered_case10173_hist_item_eval_from_results:
  5 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      (refs:hol_refs) =
      (M_success (from_cv center_environment_cv),refs) /\
  compute_eval (clock - 2)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_of_q» [from_cv boxes]) refs =
      (M_success (from_cv box_environment_cv),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv center_environment_cv;
         App «candle_cv_fs_interval_lookup» [Num 0;from_cv roots];
         App «candle_cv_fs_interval_lookup» [Num 1;from_cv roots]]) refs =
      (M_success (from_cv center_first),refs) /\
  compute_eval (clock - 4)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv box_environment_cv;
         App «candle_cv_fs_interval_lookup» [Num 2;from_cv roots];
         App «candle_cv_fs_interval_lookup» [Num 3;from_cv roots]]) refs =
      (M_success (from_cv box_second),refs) /\
  compute_eval (clock - 5)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_fixed»
        [App «candle_cv_fs_result_complete_rounded»
          [App «candle_cv_fs_list_of_q» [from_cv radii];Num 1;
           from_cv center_first;
           App «candle_cv_fs_hist_second_hessian»
             [from_cv box_second]]]) refs =
      (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots]) refs =
    (M_success (from_cv item),refs)
Proof
  strip_tac
  >> simp [registered_case10173_hist_item_unfold]
  >> simp
       [registered_case10173_hist_item_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv center_environment_cv`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv box_environment_cv`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv center_first`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv box_second`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
QED

val _ = export_theory ();
