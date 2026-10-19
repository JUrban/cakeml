(*****************************************************************************
 * Object refinement for fixed-scale Taylor-result addition.
 *
 * The fast checker keeps the symmetric Hessian in 21-entry compact form and
 * performs Taylor completion only at a checked boundary.  This theorem turns
 * the compact interval operations, their authenticated matrix expansion, and
 * that completion result into the exact evaluator result of the historical
 * source-level [fs_result_add].  The previous value and gradient bounds are
 * deliberately arbitrary: the historical addition recomputes them.
 *****************************************************************************)
Theory compute_registeredCase10173ResultAddObjectEval
Ancestors
  compute_registeredCase10173ResultAddEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_interval_add_object_eval:
  bounded_interval64_add left right = SOME result /\
  4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [from_cv (bounded_interval64_object_cv left);
         from_cv (bounded_interval64_object_cv right)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> simp []
QED

Theorem registered_case10173_fs_hessian_add_object_eval:
  bounded_interval64_list_add left right = SOME result /\
  bounded_hessian64_rows left = SOME left_rows /\
  bounded_hessian64_rows right = SOME right_rows /\
  bounded_hessian64_rows result = SOME result_rows /\
  SUM (MAP LENGTH left_rows) + LENGTH left_rows + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_matrix_add»
        [from_cv (bounded_interval64_object_cv_matrix left_rows);
         from_cv (bounded_interval64_object_cv_matrix right_rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix result_rows)),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistoricalSecondOrderMatrixEvalTheory.registered_case10173_fs_interval_matrix_add_typed_eval
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_hessian64_rows_add
  >> simp []
QED

Theorem registered_case10173_fs_result_add_object_eval:
  bounded_interval64_add
      left_center_value right_center_value = SOME center_value /\
  bounded_interval64_list_add
      left_center_gradient right_center_gradient = SOME center_gradient /\
  bounded_interval64_list_add
      left_hessian right_hessian = SOME hessian /\
  bounded_hessian64_rows left_hessian = SOME left_hessian_rows /\
  bounded_hessian64_rows right_hessian = SOME right_hessian_rows /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_object_fs_taylor_complete radii T center_value center_gradient
      hessian hessian_rows = SOME result /\
  2 < clock /\
  4 < clock - 1 /\
  LENGTH left_center_gradient + 5 < clock - 1 /\
  SUM (MAP LENGTH left_hessian_rows) + LENGTH left_hessian_rows + 5 <
      clock - 1 /\
  256 *
      (2 * LENGTH radii + LENGTH hessian_rows +
       LENGTH center_gradient + 2) < clock - 1 ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_add»
        [from_cv
           (registered_case10173_word64_object_cv_list radii);
         from_cv
           (Pair (Num 1)
             (Pair
               (Pair
                 (bounded_interval64_object_cv left_center_value)
                 (bounded_interval64_object_cv_list left_center_gradient))
               (Pair left_value_bound
                 (Pair left_gradient_bounds
                   (bounded_interval64_object_cv_matrix
                     left_hessian_rows)))));
         from_cv
           (Pair (Num 1)
             (Pair
               (Pair
                 (bounded_interval64_object_cv right_center_value)
                 (bounded_interval64_object_cv_list right_center_gradient))
               (Pair right_value_bound
                 (Pair right_gradient_bounds
                   (bounded_interval64_object_cv_matrix
                     right_hessian_rows)))))])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173ResultAddEvalTheory.registered_case10173_fs_result_add_true_eval_from_results
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `bounded_interval64_object_cv_list center_gradient`
  >> qexists_tac `bounded_interval64_object_cv center_value`
  >> qexists_tac `bounded_interval64_object_cv_matrix hessian_rows`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_add_object_eval
      >> simp [])
  >> conj_tac
  >- (irule registered_case10173_fs_hessian_add_object_eval
      >> conj_tac >- asm_rewrite_tac []
      >> qexists_tac `left_hessian`
      >> qexists_tac `hessian`
      >> qexists_tac `right_hessian`
      >> fs [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderListEvalTheory.registered_case10173_fs_interval_list_add_typed_eval
      >> asm_rewrite_tac [])
  >> irule
       (SIMP_RULE std_ss
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
         (Q.INST [`result_domain` |-> `T`, `hessian` |-> `hessian`]
           compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval))
  >> asm_rewrite_tac []
  >> qexists_tac `hessian`
  >> fs []
QED

val _ = export_theory ();
