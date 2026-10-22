(*****************************************************************************
 * Clock-uniform object contracts for the authenticated ordinary trace.
 *
 * The ordinary prefix/suffix trace theorems consume [eval_above] facts.  This
 * layer packages the checked radii projection and compact Taylor-result
 * addition refinements at that interface, so packet proofs need no evaluator
 * clock arithmetic and never fall back to closed generic source execution.
 *****************************************************************************)
Theory compute_registeredCase10173ResultAddAboveEval
Ancestors
  compute_registeredCase10173ResultAddObjectEval
  compute_registeredCase10173OrdinaryStepAboveEval
  compute_registeredCase10173RadiiEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_list_of_q_projection_eval_above:
  LENGTH items + 1 <= numeric_floor ==>
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q»
        [from_cv (registered_case10173_q_cv_list items)])
      (registered_case10173_q_numerator_cv_list items)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       compute_registeredCase10173RadiiEvalTheory.registered_case10173_fs_list_of_q_projection_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_add_object_eval_above:
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
  6 <= numeric_floor /\
  LENGTH left_center_gradient + 6 <= numeric_floor /\
  SUM (MAP LENGTH left_hessian_rows) + LENGTH left_hessian_rows + 6 <=
      numeric_floor /\
  256 *
      (2 * LENGTH radii + LENGTH hessian_rows +
       LENGTH center_gradient + 2) + 1 <= numeric_floor ==>
  registered_case10173_eval_above numeric_floor
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
      result
Proof
  strip_tac
  >> simp_tac std_ss
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       compute_registeredCase10173ResultAddObjectEvalTheory.registered_case10173_fs_result_add_object_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `center_gradient`
  >> qexists_tac `center_value`
  >> qexists_tac `hessian`
  >> qexists_tac `hessian_rows`
  >> qexists_tac `left_hessian`
  >> qexists_tac `right_hessian`
  >> conj_tac >- intLib.ARITH_TAC
  >> asm_rewrite_tac []
QED

(* The packed checker accumulates source terms in the compact Taylor-state
 * representation.  This bridge exposes one such checked transition at the
 * exact historical source boundary.  The intermediate value and gradient
 * bounds may differ because [fs_result_add] deliberately recomputes them;
 * only the authenticated center jet and Hessian feed that recomputation. *)
Theorem registered_case10173_deferred_add_object_eval_above:
  bounded_case10173_deferred_add
      (BoundedTaylor64 T left_center_value left_center_gradient
        left_value_bound left_gradient_bounds left_hessian)
      (BoundedTaylor64 T right_center_value right_center_gradient
        right_value_bound right_gradient_bounds right_hessian) =
    SOME
      (BoundedTaylor64 T center_value center_gradient
        value_bound gradient_bounds hessian) /\
  bounded_hessian64_rows left_hessian = SOME left_hessian_rows /\
  bounded_hessian64_rows right_hessian = SOME right_hessian_rows /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_taylor64_complete_decimal radii T center_value center_gradient
      hessian = SOME completed /\
  6 <= numeric_floor /\
  LENGTH left_center_gradient + 6 <= numeric_floor /\
  SUM (MAP LENGTH left_hessian_rows) + LENGTH left_hessian_rows + 6 <=
      numeric_floor /\
  256 *
      (2 * LENGTH radii + LENGTH hessian_rows +
       LENGTH center_gradient + 2) + 1 <= numeric_floor ==>
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_add»
        [from_cv
           (registered_case10173_word64_object_cv_list radii);
         from_cv
           (bounded_taylor64_rows_object_cv
             (BoundedTaylor64 T left_center_value left_center_gradient
               left_value_bound left_gradient_bounds left_hessian)
             left_hessian_rows);
         from_cv
           (bounded_taylor64_rows_object_cv
             (BoundedTaylor64 T right_center_value right_center_gradient
               right_value_bound right_gradient_bounds right_hessian)
             right_hessian_rows)])
      (bounded_taylor64_rows_object_cv completed hessian_rows)
Proof
  strip_tac
  >> `bounded_interval64_add left_center_value right_center_value =
        SOME center_value /\
      bounded_interval64_list_add left_center_gradient
        right_center_gradient = SOME center_gradient /\
      bounded_interval64_list_add left_hessian right_hessian =
        SOME hessian` by
       (fs
          [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_add_def,
           compute_boundedTaylorStateTheory.bounded_taylor64_add_def,
           compute_boundedTaylorStateTheory.bounded_taylor64_add_unchecked_def]
        >> every_case_tac
        >> gvs [])
  >> `bounded_object_fs_taylor_complete radii T center_value
        center_gradient hessian hessian_rows =
      SOME (bounded_taylor64_rows_object_cv completed hessian_rows)` by
       (irule
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact
        >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
        COND_CLAUSES]
  >> irule registered_case10173_fs_result_add_object_eval_above
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `center_gradient`
  >> qexists_tac `center_value`
  >> qexists_tac `hessian`
  >> qexists_tac `hessian_rows`
  >> qexists_tac `left_hessian`
  >> qexists_tac `right_hessian`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
