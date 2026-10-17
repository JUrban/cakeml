(*****************************************************************************
 * Registered evaluator seams around historical Taylor completion.
 *
 * The second-order Hessian projection and fixed-item wrapper are structural.
 * Proving them here leaves the object-refinement ledger with only the actual
 * radii conversion and rounded Taylor completion computations.
 *****************************************************************************)
Theory compute_registeredCase10173HistCompletionEval
Ancestors
  compute_registeredCase10173HistItemObjectEval
Libs
  bossLib preamble

Definition registered_case10173_fs_hist_second_hessian_body_def:
  registered_case10173_fs_hist_second_hessian_body =
    Uop Snd (Uop Snd (Var «second»))
End

Definition registered_case10173_fsa_item_fixed_body_def:
  registered_case10173_fsa_item_fixed_body =
    Pair (Num 1) (Var «result»)
End

Theorem registered_case10173_fs_hist_second_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_hessian» =
    SOME ([«second»],registered_case10173_fs_hist_second_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsa_item_fixed_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsa_item_fixed» =
    SOME ([«result»],registered_case10173_fsa_item_fixed_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_second_hessian_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_hessian»
        [from_cv
          (Pair (value:cv) (Pair (gradient:cv) (hessian:cv)) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv hessian),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_second_hessian_lookup,
        registered_case10173_fs_hist_second_hessian_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fsa_item_fixed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_fixed» [from_cv result])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fsa_item_fixed_lookup,
        registered_case10173_fsa_item_fixed_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_hist_completion_eval_from_results:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv radii])
      (refs:hol_refs) =
    (M_success (from_cv fixed_radii),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_hessian»
        [from_cv
          (Pair (box_value:cv)
            (Pair (box_gradient:cv) (box_hessian:cv)) : cv)]) refs =
    (M_success (from_cv box_hessian),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv fixed_radii;from_cv (Num 1);from_cv center_first;
         from_cv box_hessian]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_fixed»
        [App «candle_cv_fs_result_complete_rounded»
          [App «candle_cv_fs_list_of_q» [from_cv radii];Num 1;
           from_cv center_first;
           App «candle_cv_fs_hist_second_hessian»
             [from_cv
               (Pair (box_value:cv)
                 (Pair (box_gradient:cv) (box_hessian:cv)) : cv)]]]) refs =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  strip_tac
  >> qsuff_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [App «candle_cv_fs_list_of_q» [from_cv radii];Num 1;
             from_cv center_first;
             App «candle_cv_fs_hist_second_hessian»
               [from_cv
                 (Pair (box_value:cv)
                   (Pair (box_gradient:cv) (box_hessian:cv)) : cv)]]) refs =
        compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv fixed_radii;from_cv (Num 1);from_cv center_first;
             from_cv box_hessian]) refs`
  >- (strip_tac
      >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_fs_result_complete_rounded»
              [App «candle_cv_fs_list_of_q» [from_cv radii];Num 1;
               from_cv center_first;
               App «candle_cv_fs_hist_second_hessian»
                 [from_cv
                   (Pair (box_value:cv)
                     (Pair (box_gradient:cv) (box_hessian:cv)) : cv)]]) refs =
          (M_success (from_cv result),refs)` by fs []
      >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_fsa_item_fixed»
              [App «candle_cv_fs_result_complete_rounded»
                [App «candle_cv_fs_list_of_q» [from_cv radii];Num 1;
                 from_cv center_first;
                 App «candle_cv_fs_hist_second_hessian»
                   [from_cv
                     (Pair (box_value:cv)
                       (Pair (box_gradient:cv) (box_hessian:cv)) : cv)]]]) refs =
          compute_eval clock registered_case10173_historical_chunk16_ceqs
            (App «candle_cv_fsa_item_fixed» [from_cv result]) refs` by
           (irule
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
            >> fs [])
      >> fs [registered_case10173_fsa_item_fixed_eval])
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
  >> conj_tac >- fs []
  >> conj_tac >- fs []
  >> conj_tac
  >- (simp [compute_execTheory.from_cv_def]
      >> irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.SPEC `(Num 1:cv)`
            compute_execProofTheory.compute_eval_from_cv)))
  >> conj_tac
  >- (irule compute_execProofTheory.compute_eval_from_cv)
  >> fs []
QED

val _ = export_theory ();
