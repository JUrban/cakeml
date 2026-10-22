(*****************************************************************************
 * Object refinement for the primitive Hessian contributions in the
 * historical Taylor product.
 *
 * The literal source projects value bounds, gradient bounds, and Hessian
 * rows from its two operands.  It then forms two scaled Hessians and two
 * ordered gradient outer products.  These theorems authenticate those four
 * leaves independently of the later raw matrix additions.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulHessianLeafEval
Ancestors
  compute_registeredCase10173ResultMulCenterEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_mul_result_value_bound_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_value_bound»
        [from_cv
          (registered_case10173_mul_result_object_cv
            center_value64 center_gradient64 value_bound64 gradient_bounds64
            hessian_rows)]) (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv value_bound64)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_object_cv_def]
  >> irule
       (Q.INST
         [`result_domain:cv` |-> `(Num 1:cv)`,
          `center:cv` |->
            `Pair (bounded_interval64_object_cv center_value64)
              (bounded_interval64_object_cv_list center_gradient64)`,
          `value_bound:cv` |->
            `bounded_interval64_object_cv value_bound64`,
          `gradient_bounds:cv` |->
            `bounded_interval64_object_cv_list gradient_bounds64`,
          `hessian:cv` |->
            `bounded_interval64_object_cv_matrix hessian_rows`]
         compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_value_bound_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_mul_result_gradient_bounds_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_gradient_bounds»
        [from_cv
          (registered_case10173_mul_result_object_cv
            center_value64 center_gradient64 value_bound64 gradient_bounds64
            hessian_rows)]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_list gradient_bounds64)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_object_cv_def]
  >> irule
       (Q.INST
         [`result_domain:cv` |-> `(Num 1:cv)`,
          `center:cv` |->
            `Pair (bounded_interval64_object_cv center_value64)
              (bounded_interval64_object_cv_list center_gradient64)`,
          `value_bound:cv` |->
            `bounded_interval64_object_cv value_bound64`,
          `gradient_bounds:cv` |->
            `bounded_interval64_object_cv_list gradient_bounds64`,
          `hessian:cv` |->
            `bounded_interval64_object_cv_matrix hessian_rows`]
         compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_gradient_bounds_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_mul_result_hessian_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_hessian»
        [from_cv
          (registered_case10173_mul_result_object_cv
            center_value64 center_gradient64 value_bound64 gradient_bounds64
            hessian_rows)]) (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_matrix hessian_rows)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_object_cv_def]
  >> irule
       (Q.INST
         [`result_domain:cv` |-> `(Num 1:cv)`,
          `center:cv` |->
            `Pair (bounded_interval64_object_cv center_value64)
              (bounded_interval64_object_cv_list center_gradient64)`,
          `value_bound:cv` |->
            `bounded_interval64_object_cv value_bound64`,
          `gradient_bounds:cv` |->
            `bounded_interval64_object_cv_list gradient_bounds64`,
          `hessian:cv` |->
            `bounded_interval64_object_cv_matrix hessian_rows`]
         compute_registeredCase10173ResultAccessorEvalTheory.registered_case10173_fs_result_hessian_eval)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_mul_hessian_scale_object_eval:
  registered_case10173_fs_raw_interval_matrix_scale_object
      (bounded_interval64_object_cv scalar_value_bound)
      (MAP (MAP bounded_interval64_object_cv) matrix_hessian_rows) =
    SOME raw_scaled_rows /\
  SUM (MAP LENGTH matrix_hessian_rows) + LENGTH matrix_hessian_rows + 6 <
    clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_scale»
        [App «candle_cv_fs_result_value_bound»
           [from_cv
             (registered_case10173_mul_result_object_cv
               scalar_center_value scalar_center_gradient scalar_value_bound
               scalar_gradient_bounds scalar_hessian_rows)];
         App «candle_cv_fs_result_hessian»
           [from_cv
             (registered_case10173_mul_result_object_cv
               matrix_center_value matrix_center_gradient matrix_value_bound
               matrix_gradient_bounds matrix_hessian_rows)]])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_matrix raw_scaled_rows)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_matrix_scale»
            [from_cv (bounded_interval64_object_cv scalar_value_bound);
             from_cv
               (bounded_interval64_object_cv_matrix matrix_hessian_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_mul_result_value_bound_eval
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_mul_result_hessian_eval
      >> intLib.ARITH_TAC)
  >> rw
       [GSYM compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_map_bounded_interval64_object_cv]
  >> irule
       compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_scale_object_eval
  >> simp [listTheory.MAP_MAP_o, combinTheory.o_DEF]
  >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_mul_gradient_outer_object_eval:
  registered_case10173_fs_raw_interval_outer_object
      (MAP bounded_interval64_object_cv left_gradient_bounds)
      (MAP bounded_interval64_object_cv right_gradient_bounds) =
    SOME raw_outer_rows /\
  LENGTH left_gradient_bounds * (LENGTH right_gradient_bounds + 1) + 7 <
    clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_outer»
        [App «candle_cv_fs_result_gradient_bounds»
           [from_cv
             (registered_case10173_mul_result_object_cv
               left_center_value left_center_gradient left_value_bound
               left_gradient_bounds left_hessian_rows)];
         App «candle_cv_fs_result_gradient_bounds»
           [from_cv
             (registered_case10173_mul_result_object_cv
               right_center_value right_center_gradient right_value_bound
               right_gradient_bounds right_hessian_rows)]])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_matrix raw_outer_rows)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_outer»
            [from_cv
               (bounded_interval64_object_cv_list left_gradient_bounds);
             from_cv
               (bounded_interval64_object_cv_list right_gradient_bounds)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_mul_result_gradient_bounds_eval
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_mul_result_gradient_bounds_eval
      >> intLib.ARITH_TAC)
  >> rw
       [GSYM compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv]
  >> irule
       compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
