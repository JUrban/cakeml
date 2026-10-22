(*****************************************************************************
 * Complete object refinement for the historical Taylor product.
 *
 * This composes the exact source domain, center, and Hessian traces with the
 * single final [fs_result_complete_raw] rounding boundary.  The theorem is
 * intentionally stated over the raw trace witnesses; the following typed
 * refinement layer will derive those witnesses from the fast decimal
 * product checker.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulObjectEval
Ancestors
  compute_registeredCase10173ResultMulHessianEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_result_mul_object_eval:
  bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv left_center_value)
      (bounded_interval64_object_cv right_center_value) =
    SOME (Pair raw_center_lower raw_center_upper) /\
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv right_center_value)
      (MAP bounded_interval64_object_cv left_center_gradient) =
    SOME raw_left_center_gradient /\
  registered_case10173_fs_raw_interval_list_scale_object
      (bounded_interval64_object_cv left_center_value)
      (MAP bounded_interval64_object_cv right_center_gradient) =
    SOME raw_right_center_gradient /\
  registered_case10173_fs_raw_interval_list_add_object
      raw_left_center_gradient raw_right_center_gradient =
    SOME raw_center_gradient /\
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
      raw_left_half raw_right_half = SOME raw_hessian_objects /\
  bounded_object_fs_raw_interval_round 1000000000000
      (Pair raw_center_lower raw_center_upper) =
    SOME (bounded_interval64_object_cv result_center_value) /\
  registered_case10173_fs_raw_interval_list_round_object
      1000000000000 raw_center_gradient =
    SOME (MAP bounded_interval64_object_cv result_center_gradient) /\
  registered_case10173_fs_raw_interval_matrix_round_object
      1000000000000 raw_hessian_objects =
    SOME (MAP (MAP bounded_interval64_object_cv) result_hessian_rows) /\
  bounded_hessian64_rows result_hessian = SOME result_hessian_rows /\
  bounded_object_fs_taylor_complete radii T result_center_value
      result_center_gradient result_hessian result_hessian_rows =
    SOME result_object /\
  1 < clock - 1 /\
  LENGTH left_center_gradient + 7 < clock - 1 /\
  LENGTH right_center_gradient + 7 < clock - 1 /\
  LENGTH raw_left_center_gradient + 7 < clock - 1 /\
  SUM (MAP LENGTH left_hessian_rows) + LENGTH left_hessian_rows + 6 <
    clock - 1 /\
  SUM (MAP LENGTH right_hessian_rows) + LENGTH right_hessian_rows + 6 <
    clock - 1 /\
  LENGTH left_gradient_bounds * (LENGTH right_gradient_bounds + 1) + 7 <
    clock - 1 /\
  LENGTH right_gradient_bounds * (LENGTH left_gradient_bounds + 1) + 7 <
    clock - 1 /\
  SUM (MAP LENGTH raw_scaled_left_hessian) +
      LENGTH raw_scaled_left_hessian + 5 < clock - 1 /\
  SUM (MAP LENGTH raw_right_outer_left) + LENGTH raw_right_outer_left + 5 <
    clock - 1 /\
  SUM (MAP LENGTH raw_left_half) + LENGTH raw_left_half + 5 < clock - 1 /\
  LENGTH raw_center_gradient + 13 < clock - 1 /\
  SUM (MAP LENGTH raw_hessian_objects) + LENGTH raw_hessian_objects + 13 <
    clock - 1 /\
  256 *
      (2 * LENGTH radii + LENGTH result_hessian_rows +
       LENGTH result_center_gradient + 2) + 1 < clock - 1 ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_mul»
        [from_cv
           (registered_case10173_word64_object_cv_list radii);
         from_cv
           (registered_case10173_mul_result_object_cv
             left_center_value left_center_gradient left_value_bound
             left_gradient_bounds left_hessian_rows);
         from_cv
           (registered_case10173_mul_result_object_cv
             right_center_value right_center_gradient right_value_bound
             right_gradient_bounds right_hessian_rows)])
      (refs:hol_refs) =
    (M_success (from_cv result_object),refs)
Proof
  strip_tac
  >> match_mp_tac
       (Q.INST
         [`radii:cv` |->
            `registered_case10173_word64_object_cv_list rads`,
          `left:cv` |->
            `registered_case10173_mul_result_object_cv
              left_center_value left_center_gradient left_value_bound
              left_gradient_bounds left_hessian_rows`,
          `right:cv` |->
            `registered_case10173_mul_result_object_cv
              right_center_value right_center_gradient right_value_bound
              right_gradient_bounds right_hessian_rows`,
          `result_domain:cv` |-> `Num 1`,
          `raw_center:cv` |->
            `Pair (Pair raw_center_lower raw_center_upper)
              (registered_case10173_cv_list raw_center_gradient)`,
          `raw_hessian:cv` |->
            `registered_case10173_cv_matrix raw_hessian_objects`,
          `result:cv` |-> `result_object`]
         compute_registeredCase10173ResultMulEvalTheory.registered_case10173_fs_result_mul_eval_from_components)
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (match_mp_tac
        (Q.INST
          [`radii:cv` |->
             `registered_case10173_word64_object_cv_list rads`]
          compute_registeredCase10173ResultMulCenterEvalTheory.registered_case10173_fs_result_mul_true_domain_object_eval)
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (match_mp_tac
        (Q.INST
          [`radii:cv` |->
             `registered_case10173_word64_object_cv_list rads`,
           `raw_left_gradient:cv list` |-> `raw_left_center_gradient`,
           `raw_right_gradient:cv list` |-> `raw_right_center_gradient`]
          compute_registeredCase10173ResultMulCenterEvalTheory.registered_case10173_fs_result_mul_center_object_eval)
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (match_mp_tac
        (Q.INST
          [`radii:cv` |->
             `registered_case10173_word64_object_cv_list rads`,
           `raw_hessian:cv list list` |-> `raw_hessian_objects`]
          compute_registeredCase10173ResultMulHessianEvalTheory.registered_case10173_fs_result_mul_hessian_object_eval)
      >> asm_rewrite_tac [])
  >> match_mp_tac
       (SIMP_RULE std_ss
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def]
         (Q.INST
           [`raw_center_value:cv` |->
              `Pair raw_center_lower raw_center_upper`,
            `raw_hessian:cv list list` |-> `raw_hessian_objects`,
            `result_domain:bool` |-> `T`,
            `center_value:bounded_interval64` |-> `result_center_value`,
            `center_gradient:bounded_interval64 list` |->
              `result_center_gradient`,
            `hessian:bounded_interval64 list` |-> `result_hessian`,
            `hessian_rows:bounded_interval64 list list` |->
              `result_hessian_rows`,
            `result:cv` |-> `result_object`]
           compute_registeredCase10173ResultCompleteRawEvalTheory.registered_case10173_fs_result_complete_raw_object_eval))
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
