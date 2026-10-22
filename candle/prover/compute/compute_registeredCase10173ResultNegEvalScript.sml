(*****************************************************************************
 * Registered evaluator contract for fixed-scale Taylor-result negation.
 *
 * The literal source negates the center jet and expanded Hessian, then
 * recomputes the value and gradient bounds through decimal Taylor
 * completion.  This theorem keeps that numerical boundary explicit; it does
 * not identify the decimal completion with the older dyadic helper.
 *****************************************************************************)
Theory compute_registeredCase10173ResultNegEval
Ancestors
  compute_registeredCase10173HistoricalNegListEval
  compute_registeredCase10173ResultAccessorEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_neg_body_def:
  registered_case10173_fs_result_neg_body =
    App «candle_cv_fs_result_complete_rounded»
      [Var «radii»;
       App «candle_cv_fs_result_domain» [Var «result»];
       App «candle_cv_fs_first_make»
         [App «candle_cv_fs_interval_neg»
            [App «candle_cv_fs_first_value»
               [App «candle_cv_fs_result_center» [Var «result»]]];
          App «candle_cv_fs_interval_list_neg»
            [App «candle_cv_fs_first_gradient»
               [App «candle_cv_fs_result_center» [Var «result»]]]];
       App «candle_cv_fs_interval_matrix_neg»
         [App «candle_cv_fs_result_hessian» [Var «result»]]]
End

Theorem registered_case10173_fs_result_neg_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_neg» =
    SOME
      ([«radii»;«result»],registered_case10173_fs_result_neg_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_neg_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_neg»
        [from_cv radii;from_cv result]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«radii»,from_cv radii);(«result»,from_cv result)]
        registered_case10173_fs_result_neg_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_result_neg_lookup]
QED

Theorem registered_case10173_fs_result_neg_center_value_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv (center_value:cv)])
      (refs:hol_refs) = (M_success (from_cv (neg_center_value:cv)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_first_value»
          [App «candle_cv_fs_result_center»
            [from_cv
              ((Pair (result_domain:cv)
                (Pair (Pair center_value center_gradient)
                  (Pair value_bound
                    (Pair gradient_bounds hessian)))):cv)]]]) refs =
    (M_success (from_cv neg_center_value),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv center_value]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- asm_rewrite_tac []
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_value_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_neg_center_gradient_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_neg» [from_cv (center_gradient:cv)])
      (refs:hol_refs) = (M_success (from_cv (neg_center_gradient:cv)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_neg»
        [App «candle_cv_fs_first_gradient»
          [App «candle_cv_fs_result_center»
            [from_cv
              ((Pair (result_domain:cv)
                (Pair (Pair center_value center_gradient)
                  (Pair value_bound
                    (Pair gradient_bounds hessian)))):cv)]]]) refs =
    (M_success (from_cv neg_center_gradient),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_list_neg»
            [from_cv center_gradient]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- asm_rewrite_tac []
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_center_gradient_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_neg_center_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv (center_value:cv)])
      (refs:hol_refs) = (M_success (from_cv (neg_center_value:cv)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_neg» [from_cv center_gradient]) refs =
    (M_success (from_cv neg_center_gradient),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [App «candle_cv_fs_interval_neg»
          [App «candle_cv_fs_first_value»
            [App «candle_cv_fs_result_center»
              [from_cv
                ((Pair (result_domain:cv)
                  (Pair (Pair center_value center_gradient)
                    (Pair value_bound
                      (Pair gradient_bounds hessian)))):cv)]]];
         App «candle_cv_fs_interval_list_neg»
          [App «candle_cv_fs_first_gradient»
            [App «candle_cv_fs_result_center»
              [from_cv
                ((Pair (result_domain:cv)
                  (Pair (Pair center_value center_gradient)
                    (Pair value_bound
                      (Pair gradient_bounds hessian)))):cv)]]]]) refs =
    (M_success (from_cv (Pair neg_center_value neg_center_gradient)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv neg_center_value;from_cv neg_center_gradient]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- (irule registered_case10173_fs_result_neg_center_value_eval
          >> asm_rewrite_tac [])
      >> irule registered_case10173_fs_result_neg_center_gradient_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_neg_hessian_eval:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_neg» [from_cv (hessian:cv)])
      (refs:hol_refs) = (M_success (from_cv (neg_hessian:cv)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_neg»
        [App «candle_cv_fs_result_hessian»
          [from_cv
            ((Pair (result_domain:cv)
              (Pair center
                (Pair value_bound (Pair gradient_bounds hessian)))):cv)]]) refs =
    (M_success (from_cv neg_hessian),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_matrix_neg» [from_cv hessian]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- asm_rewrite_tac []
      >> irule
           compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_hessian_eval
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_neg_true_eval_from_results:
  2 < clock /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [from_cv center_value])
      (refs:hol_refs) = (M_success (from_cv neg_center_value),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_list_neg» [from_cv center_gradient]) refs =
    (M_success (from_cv neg_center_gradient),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_neg» [from_cv hessian]) refs =
    (M_success (from_cv neg_hessian),refs) /\
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv radii;from_cv (Num 1);
         from_cv (Pair neg_center_value neg_center_gradient);
         from_cv neg_hessian]) refs =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_neg»
        [from_cv radii;
         from_cv
           (Pair (Num 1)
             (Pair (Pair center_value center_gradient)
               (Pair value_bound (Pair gradient_bounds hessian))))]) refs =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fs_result_neg_unfold]
  >> simp
       [registered_case10173_fs_result_neg_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv radii;Num 1;
             Pair (from_cv neg_center_value)
               (from_cv neg_center_gradient);
             from_cv neg_hessian]) refs`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`result2:cv` |-> `Num 1`,
             `result3:cv` |->
               `Pair neg_center_value neg_center_gradient`]
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results))
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`result_domain:cv` |-> `Num 1`,
                 `center:cv` |-> `Pair center_value center_gradient`]
                compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_domain_eval))
          >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`result_domain:cv` |-> `Num 1`]
                registered_case10173_fs_result_neg_center_eval))
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`result_domain:cv` |-> `Num 1`,
                `center:cv` |-> `Pair center_value center_gradient`]
               registered_case10173_fs_result_neg_hessian_eval))
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> fs [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_bounded_hessian64_rows_neg:
  bounded_hessian64_rows hessian = SOME rows ==>
  bounded_hessian64_rows (bounded_interval64_list_neg hessian) =
    SOME (MAP bounded_interval64_list_neg rows)
Proof
  rw
    [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def,
     compute_boundedIntervalListTheory.bounded_interval64_list_neg_def]
  >> every_case_tac
  >> gvs [compute_boundedIntervalListTheory.bounded_interval64_list_neg_def]
QED

Theorem registered_case10173_fs_result_neg_object_eval:
  bounded_hessian64_rows source_hessian = SOME source_rows /\
  bounded_object_fs_taylor_complete radii T
      (bounded_interval64_neg center_value)
      (bounded_interval64_list_neg center_gradient)
      (bounded_interval64_list_neg source_hessian)
      (MAP bounded_interval64_list_neg source_rows) = SOME result /\
  2 < clock /\
  3 < clock - 1 /\
  LENGTH center_gradient + 4 < clock - 1 /\
  SUM (MAP LENGTH source_rows) + LENGTH source_rows + 4 < clock - 1 /\
  256 *
      (2 * LENGTH radii + LENGTH source_rows +
       LENGTH center_gradient + 2) < clock - 1 ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_neg»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv
           (Pair (Num 1)
             (Pair
               (Pair (bounded_interval64_object_cv center_value)
                 (bounded_interval64_object_cv_list center_gradient))
               (Pair value_bound
                 (Pair gradient_bounds
                   (bounded_interval64_object_cv_matrix source_rows)))))])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_result_neg_true_eval_from_results
  >> conj_tac >- asm_rewrite_tac []
  >> qexistsl_tac
       [`bounded_interval64_object_cv_list
          (bounded_interval64_list_neg center_gradient)`,
        `bounded_interval64_object_cv
          (bounded_interval64_neg center_value)`,
        `bounded_interval64_object_cv_matrix
          (MAP bounded_interval64_list_neg source_rows)`]
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalNegListEvalTheory.registered_case10173_fs_interval_matrix_neg_typed_eval
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalNegListEvalTheory.registered_case10173_fs_interval_list_neg_typed_eval
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
      >> simp
           [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact])
  >> irule
       (SIMP_RULE std_ss
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
         (Q.INST
           [`result_domain` |-> `T`,
            `center_value` |-> `bounded_interval64_neg center_value`,
            `center_gradient` |->
              `bounded_interval64_list_neg center_gradient`,
            `hessian` |-> `bounded_interval64_list_neg source_hessian`,
            `rows` |-> `MAP bounded_interval64_list_neg source_rows`]
           compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval))
  >> asm_rewrite_tac []
  >> conj_tac
  >- fs
       [compute_boundedIntervalListTheory.bounded_interval64_list_neg_length,
        listTheory.LENGTH_MAP]
  >> qexists_tac `source_hessian`
  >> asm_rewrite_tac []
  >> irule registered_case10173_bounded_hessian64_rows_neg
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
