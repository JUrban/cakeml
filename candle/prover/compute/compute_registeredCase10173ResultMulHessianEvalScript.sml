(*****************************************************************************
 * Object refinement for the complete raw Hessian of the historical Taylor
 * product.
 *
 * This follows the source's exact association:
 *   (right.value * left.hessian + outer left.grad right.grad) +
 *   (outer right.grad left.grad + left.value * right.hessian).
 * All entries remain unrounded cv integers.  Rounding is performed only by
 * the later [fs_result_complete_raw] call.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulHessianEval
Ancestors
  compute_registeredCase10173ResultMulHessianLeafEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_raw_interval_matrix_add_from_results:
  0 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv (registered_case10173_cv_matrix left_rows)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success (from_cv (registered_case10173_cv_matrix right_rows)),refs) /\
  registered_case10173_fs_raw_interval_matrix_add_object
      left_rows right_rows = SOME result_rows /\
  SUM (MAP LENGTH left_rows) + LENGTH left_rows + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_add»
        [left_expression;right_expression]) refs =
    (M_success
      (from_cv (registered_case10173_cv_matrix result_rows)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_matrix_add»
            [from_cv (registered_case10173_cv_matrix left_rows);
             from_cv (registered_case10173_cv_matrix right_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173HistoricalRawMatrixAddEvalTheory.registered_case10173_fs_raw_interval_matrix_add_object_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_mul_hessian_left_half_object_eval:
  registered_case10173_fs_raw_interval_matrix_scale_object
      (bounded_interval64_object_cv right_value_bound)
      (MAP (MAP bounded_interval64_object_cv) left_hessian_rows) =
    SOME raw_scaled_left_hessian /\
  registered_case10173_fs_raw_interval_outer_object
      (MAP bounded_interval64_object_cv left_gradient_bounds)
      (MAP bounded_interval64_object_cv right_gradient_bounds) =
    SOME raw_left_outer_right /\
  registered_case10173_fs_raw_interval_matrix_add_object
      raw_scaled_left_hessian raw_left_outer_right = SOME raw_left_half /\
  SUM (MAP LENGTH left_hessian_rows) + LENGTH left_hessian_rows + 6 <
    clock /\
  LENGTH left_gradient_bounds * (LENGTH right_gradient_bounds + 1) + 7 <
    clock /\
  SUM (MAP LENGTH raw_scaled_left_hessian) +
      LENGTH raw_scaled_left_hessian + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_add»
        [App «candle_cv_fs_raw_interval_matrix_scale»
           [App «candle_cv_fs_result_value_bound»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  right_center_value right_center_gradient right_value_bound
                  right_gradient_bounds right_hessian_rows)];
            App «candle_cv_fs_result_hessian»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  left_center_value left_center_gradient left_value_bound
                  left_gradient_bounds left_hessian_rows)]];
         App «candle_cv_fs_raw_interval_outer»
           [App «candle_cv_fs_result_gradient_bounds»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  left_center_value left_center_gradient left_value_bound
                  left_gradient_bounds left_hessian_rows)];
            App «candle_cv_fs_result_gradient_bounds»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  right_center_value right_center_gradient right_value_bound
                  right_gradient_bounds right_hessian_rows)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_matrix raw_left_half)),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_raw_interval_matrix_add_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `raw_scaled_left_hessian`
  >> qexists_tac `raw_left_outer_right`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        compute_registeredCase10173ResultMulHessianLeafEvalTheory.registered_case10173_fs_result_mul_hessian_scale_object_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173ResultMulHessianLeafEvalTheory.registered_case10173_fs_result_mul_gradient_outer_object_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_mul_hessian_right_half_object_eval:
  registered_case10173_fs_raw_interval_outer_object
      (MAP bounded_interval64_object_cv right_gradient_bounds)
      (MAP bounded_interval64_object_cv left_gradient_bounds) =
    SOME raw_right_outer_left /\
  registered_case10173_fs_raw_interval_matrix_scale_object
      (bounded_interval64_object_cv left_value_bound)
      (MAP (MAP bounded_interval64_object_cv) right_hessian_rows) =
    SOME raw_scaled_right_hessian /\
  registered_case10173_fs_raw_interval_matrix_add_object
      raw_right_outer_left raw_scaled_right_hessian = SOME raw_right_half /\
  LENGTH right_gradient_bounds * (LENGTH left_gradient_bounds + 1) + 7 <
    clock /\
  SUM (MAP LENGTH right_hessian_rows) + LENGTH right_hessian_rows + 6 <
    clock /\
  SUM (MAP LENGTH raw_right_outer_left) + LENGTH raw_right_outer_left + 5 <
    clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_add»
        [App «candle_cv_fs_raw_interval_outer»
           [App «candle_cv_fs_result_gradient_bounds»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  right_center_value right_center_gradient right_value_bound
                  right_gradient_bounds right_hessian_rows)];
            App «candle_cv_fs_result_gradient_bounds»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  left_center_value left_center_gradient left_value_bound
                  left_gradient_bounds left_hessian_rows)]];
         App «candle_cv_fs_raw_interval_matrix_scale»
           [App «candle_cv_fs_result_value_bound»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  left_center_value left_center_gradient left_value_bound
                  left_gradient_bounds left_hessian_rows)];
            App «candle_cv_fs_result_hessian»
              [from_cv
                (registered_case10173_mul_result_object_cv
                  right_center_value right_center_gradient right_value_bound
                  right_gradient_bounds right_hessian_rows)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_matrix raw_right_half)),refs)
Proof
  strip_tac
  >> irule registered_case10173_fs_raw_interval_matrix_add_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `raw_right_outer_left`
  >> qexists_tac `raw_scaled_right_hessian`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        compute_registeredCase10173ResultMulHessianLeafEvalTheory.registered_case10173_fs_result_mul_gradient_outer_object_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173ResultMulHessianLeafEvalTheory.registered_case10173_fs_result_mul_hessian_scale_object_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_mul_hessian_object_eval:
  registered_case10173_fs_raw_interval_matrix_scale_object
      (bounded_interval64_object_cv right_value_bound)
      (MAP (MAP bounded_interval64_object_cv) left_hessian_rows) =
    SOME raw_scaled_left_hessian /\
  registered_case10173_fs_raw_interval_outer_object
      (MAP bounded_interval64_object_cv left_gradient_bounds)
      (MAP bounded_interval64_object_cv right_gradient_bounds) =
    SOME raw_left_outer_right /\
  registered_case10173_fs_raw_interval_matrix_add_object
      raw_scaled_left_hessian raw_left_outer_right = SOME raw_left_half /\
  registered_case10173_fs_raw_interval_outer_object
      (MAP bounded_interval64_object_cv right_gradient_bounds)
      (MAP bounded_interval64_object_cv left_gradient_bounds) =
    SOME raw_right_outer_left /\
  registered_case10173_fs_raw_interval_matrix_scale_object
      (bounded_interval64_object_cv left_value_bound)
      (MAP (MAP bounded_interval64_object_cv) right_hessian_rows) =
    SOME raw_scaled_right_hessian /\
  registered_case10173_fs_raw_interval_matrix_add_object
      raw_right_outer_left raw_scaled_right_hessian = SOME raw_right_half /\
  registered_case10173_fs_raw_interval_matrix_add_object
      raw_left_half raw_right_half = SOME raw_hessian /\
  SUM (MAP LENGTH left_hessian_rows) + LENGTH left_hessian_rows + 6 <
    clock /\
  SUM (MAP LENGTH right_hessian_rows) + LENGTH right_hessian_rows + 6 <
    clock /\
  LENGTH left_gradient_bounds * (LENGTH right_gradient_bounds + 1) + 7 <
    clock /\
  LENGTH right_gradient_bounds * (LENGTH left_gradient_bounds + 1) + 7 <
    clock /\
  SUM (MAP LENGTH raw_scaled_left_hessian) +
      LENGTH raw_scaled_left_hessian + 5 < clock /\
  SUM (MAP LENGTH raw_right_outer_left) + LENGTH raw_right_outer_left + 5 <
    clock /\
  SUM (MAP LENGTH raw_left_half) + LENGTH raw_left_half + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («left»,from_cv
           (registered_case10173_mul_result_object_cv
             left_center_value left_center_gradient left_value_bound
             left_gradient_bounds left_hessian_rows));
         («right»,from_cv
           (registered_case10173_mul_result_object_cv
             right_center_value right_center_gradient right_value_bound
             right_gradient_bounds right_hessian_rows))]
        registered_case10173_fs_result_mul_hessian_body) (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_matrix raw_hessian)),refs)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173ResultMulEvalTheory.registered_case10173_fs_result_mul_hessian_body_def,
        compute_evalTheory.subst_def]
  >> irule registered_case10173_fs_raw_interval_matrix_add_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `raw_left_half`
  >> qexists_tac `raw_right_half`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (match_mp_tac
        registered_case10173_fs_result_mul_hessian_left_half_object_eval
      >> asm_rewrite_tac [])
  >> match_mp_tac
       registered_case10173_fs_result_mul_hessian_right_half_object_eval
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
