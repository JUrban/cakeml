(*****************************************************************************
 * Registered evaluator seam for fixed-scale Taylor-result addition.
 *
 * The historical suffix performs thirteen additions.  This theorem reduces
 * each source-level result addition to interval, list, matrix, and final
 * completion results over the exact five-field result representation.  It is
 * packet-parametric and never invokes a closed generic source replay.
 *****************************************************************************)
Theory compute_registeredCase10173ResultAddEval
Ancestors
  compute_registeredCase10173ResultAccessorEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_add_body_def:
  registered_case10173_fs_result_add_body =
    App «candle_cv_fs_result_complete_rounded»
      [Var «radii»;
       App «candle_cv_bool_and»
         [App «candle_cv_fs_result_domain» [Var «left»];
          App «candle_cv_fs_result_domain» [Var «right»]];
       App «candle_cv_fs_first_make»
         [App «candle_cv_fs_interval_add»
            [App «candle_cv_fs_first_value»
               [App «candle_cv_fs_result_center» [Var «left»]];
             App «candle_cv_fs_first_value»
               [App «candle_cv_fs_result_center» [Var «right»]]];
          App «candle_cv_fs_interval_list_add»
            [App «candle_cv_fs_first_gradient»
               [App «candle_cv_fs_result_center» [Var «left»]];
             App «candle_cv_fs_first_gradient»
               [App «candle_cv_fs_result_center» [Var «right»]]]];
       App «candle_cv_fs_interval_matrix_add»
         [App «candle_cv_fs_result_hessian» [Var «left»];
          App «candle_cv_fs_result_hessian» [Var «right»]]]
End

Theorem registered_case10173_fs_result_add_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_add» =
    SOME
      ([«radii»;«left»;«right»],
       registered_case10173_fs_result_add_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_add_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_add»
        [from_cv radii;from_cv left;from_cv right])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);(«left»,from_cv left);
         («right»,from_cv right)]
        registered_case10173_fs_result_add_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_result_add_lookup]
QED

Theorem registered_case10173_fs_result_add_true_domain_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_bool_and»
        [App «candle_cv_fs_result_domain»
           [from_cv
             (Pair (Num 1)
               (Pair left_center
                 (Pair left_value_bound
                   (Pair left_gradient_bounds left_hessian))))];
         App «candle_cv_fs_result_domain»
           [from_cv
             (Pair (Num 1)
               (Pair right_center
                 (Pair right_value_bound
                   (Pair right_gradient_bounds right_hessian))))]])
      (refs:hol_refs) =
    (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> simp [compute_execTheory.from_cv_def]
  >> irule
       compute_registeredCase10173RawWrapperEvalTheory.registered_case10173_bool_and_true_one_eval
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >> irule
       compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_true_domain_normalized_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_add_center_value_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [from_cv left_center_value;from_cv right_center_value])
      (refs:hol_refs) =
    (M_success (from_cv center_value),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_first_value»
           [App «candle_cv_fs_result_center»
             [from_cv
               (Pair left_domain
                 (Pair (Pair left_center_value left_center_gradient)
                   (Pair left_value_bound
                     (Pair left_gradient_bounds left_hessian))))]];
         App «candle_cv_fs_first_value»
           [App «candle_cv_fs_result_center»
             [from_cv
               (Pair right_domain
                 (Pair (Pair right_center_value right_center_gradient)
                   (Pair right_value_bound
                     (Pair right_gradient_bounds right_hessian))))]]]) refs =
    (M_success (from_cv center_value),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_add»
            [from_cv left_center_value;from_cv right_center_value]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_value_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_add_center_gradient_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_add»
        [from_cv left_center_gradient;from_cv right_center_gradient])
      (refs:hol_refs) =
    (M_success (from_cv center_gradient),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_add»
        [App «candle_cv_fs_first_gradient»
           [App «candle_cv_fs_result_center»
             [from_cv
               (Pair left_domain
                 (Pair (Pair left_center_value left_center_gradient)
                   (Pair left_value_bound
                     (Pair left_gradient_bounds left_hessian))))]];
         App «candle_cv_fs_first_gradient»
           [App «candle_cv_fs_result_center»
             [from_cv
               (Pair right_domain
                 (Pair (Pair right_center_value right_center_gradient)
                   (Pair right_value_bound
                     (Pair right_gradient_bounds right_hessian))))]]]) refs =
    (M_success (from_cv center_gradient),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_add»
            [from_cv left_center_gradient;from_cv right_center_gradient]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_gradient_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_add_hessian_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_add»
        [from_cv left_hessian;from_cv right_hessian])
      (refs:hol_refs) =
    (M_success (from_cv hessian),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_add»
        [App «candle_cv_fs_result_hessian»
           [from_cv
             (Pair left_domain
               (Pair left_center
                 (Pair left_value_bound
                   (Pair left_gradient_bounds left_hessian))))];
         App «candle_cv_fs_result_hessian»
           [from_cv
             (Pair right_domain
               (Pair right_center
                 (Pair right_value_bound
                   (Pair right_gradient_bounds right_hessian))))]]) refs =
    (M_success (from_cv hessian),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_matrix_add»
            [from_cv left_hessian;from_cv right_hessian]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_hessian_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_add_center_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [from_cv left_center_value;from_cv right_center_value])
      (refs:hol_refs) =
    (M_success (from_cv center_value),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_add»
        [from_cv left_center_gradient;from_cv right_center_gradient]) refs =
    (M_success (from_cv center_gradient),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [App «candle_cv_fs_interval_add»
           [App «candle_cv_fs_first_value»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (Pair left_domain
                    (Pair (Pair left_center_value left_center_gradient)
                      (Pair left_value_bound
                        (Pair left_gradient_bounds left_hessian))))]];
            App «candle_cv_fs_first_value»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (Pair right_domain
                    (Pair (Pair right_center_value right_center_gradient)
                      (Pair right_value_bound
                        (Pair right_gradient_bounds right_hessian))))]]];
         App «candle_cv_fs_interval_list_add»
           [App «candle_cv_fs_first_gradient»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (Pair left_domain
                    (Pair (Pair left_center_value left_center_gradient)
                      (Pair left_value_bound
                        (Pair left_gradient_bounds left_hessian))))]];
            App «candle_cv_fs_first_gradient»
              [App «candle_cv_fs_result_center»
                [from_cv
                  (Pair right_domain
                    (Pair (Pair right_center_value right_center_gradient)
                      (Pair right_value_bound
                        (Pair right_gradient_bounds right_hessian))))]]]]) refs =
    (M_success (from_cv (Pair center_value center_gradient)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv center_value;from_cv center_gradient]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- (irule registered_case10173_fs_result_add_center_value_eval
          >> asm_rewrite_tac [])
      >> irule registered_case10173_fs_result_add_center_gradient_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_add_true_eval_from_results:
  2 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [from_cv left_center_value;from_cv right_center_value])
      (refs:hol_refs) =
    (M_success (from_cv center_value),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_add»
        [from_cv left_center_gradient;from_cv right_center_gradient]) refs =
    (M_success (from_cv center_gradient),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_add»
        [from_cv left_hessian;from_cv right_hessian]) refs =
    (M_success (from_cv hessian),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv radii;from_cv (Num 1);
         from_cv (Pair center_value center_gradient);from_cv hessian]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_add»
        [from_cv radii;
         from_cv
           (Pair (Num 1)
             (Pair (Pair left_center_value left_center_gradient)
               (Pair left_value_bound
                 (Pair left_gradient_bounds left_hessian))));
         from_cv
           (Pair (Num 1)
             (Pair (Pair right_center_value right_center_gradient)
               (Pair right_value_bound
                 (Pair right_gradient_bounds right_hessian))))]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fs_result_add_unfold]
  >> simp
       [registered_case10173_fs_result_add_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv radii;Num 1;
             Pair (from_cv center_value) (from_cv center_gradient);
             from_cv hessian]) refs`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`result2:cv` |-> `Num 1`,
             `result3:cv` |-> `Pair center_value center_gradient`]
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`left_center:cv` |->
                   `Pair left_center_value left_center_gradient`,
                 `right_center:cv` |->
                   `Pair right_center_value right_center_gradient`]
                registered_case10173_fs_result_add_true_domain_eval))
          >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`left_domain:cv` |-> `Num 1`,
                 `right_domain:cv` |-> `Num 1`]
                registered_case10173_fs_result_add_center_eval))
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`left_domain:cv` |-> `Num 1`,
                `right_domain:cv` |-> `Num 1`,
                `left_center:cv` |->
                  `Pair left_center_value left_center_gradient`,
                `right_center:cv` |->
                  `Pair right_center_value right_center_gradient`]
               registered_case10173_fs_result_add_hessian_eval))
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> fs [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
