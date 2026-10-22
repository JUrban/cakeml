(*****************************************************************************
 * Clock-uniform typed contract for the authenticated Taylor product.
 *
 * The compact decimal product already has a complete source-contract trace.
 * This layer discharges the fixed six-dimensional shape and clock arithmetic
 * once, then exposes the literal historical [fs_result_mul] call through the
 * [eval_above] interface consumed by polynomial-program traces.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulAboveEval
Ancestors
  compute_registeredCase10173ResultMulContract
  compute_registeredCase10173OrdinaryStepAboveEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_matrix_every_transfer6:
  !source target.
    MAP LENGTH target = MAP LENGTH source /\
    EVERY (\row. LENGTH row = 6) source ==>
    EVERY (\row. LENGTH row = 6) target
Proof
  Induct
  >> Cases_on `target`
  >> rw []
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_matrix_shape_transfer6:
  MAP LENGTH target = MAP LENGTH source /\
  LENGTH source = 6 /\
  EVERY (\row. LENGTH row = 6) source ==>
  LENGTH target = 6 /\ EVERY (\row. LENGTH row = 6) target
Proof
  strip_tac
  >> conj_tac
  >- metis_tac [listTheory.LENGTH_MAP]
  >> metis_tac [registered_case10173_matrix_every_transfer6]
QED

Theorem registered_case10173_matrix_shape6_sum:
  LENGTH rows = 6 /\ EVERY (\row. LENGTH row = 6) rows ==>
  SUM (MAP LENGTH rows) = 36
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> gvs []
QED

Theorem registered_case10173_mul_result_rows_object:
  bounded_taylor64_rows_object_cv
      (BoundedTaylor64 T center center_gradient value gradient_bounds hessian)
      hessian_rows =
    registered_case10173_mul_result_object_cv center center_gradient value
      gradient_bounds hessian_rows
Proof
  simp
    [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def,
     compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
     compute_registeredCase10173ResultMulCenterEvalTheory.registered_case10173_mul_result_object_cv_def]
QED

Theorem registered_case10173_taylor_mul_decimal_eval_above:
  bounded_taylor64_mul_decimal radii
      (BoundedTaylor64 T left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedTaylor64 T right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    SOME
      (BoundedTaylor64 T result_center result_center_gradient
        result_value result_gradient_bounds result_hessian) /\
  bounded_hessian64_rows left_hessian = SOME left_hessian_rows /\
  bounded_hessian64_rows right_hessian = SOME right_hessian_rows /\
  bounded_hessian64_rows result_hessian = SOME result_hessian_rows /\
  LENGTH radii = 6 /\
  8192 <= numeric_floor ==>
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_mul»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv
           (bounded_taylor64_rows_object_cv
             (BoundedTaylor64 T left_center left_center_gradient
               left_value left_gradient_bounds left_hessian)
             left_hessian_rows);
         from_cv
           (bounded_taylor64_rows_object_cv
             (BoundedTaylor64 T right_center right_center_gradient
               right_value right_gradient_bounds right_hessian)
             right_hessian_rows)])
      (bounded_taylor64_rows_object_cv
        (BoundedTaylor64 T result_center result_center_gradient
          result_value result_gradient_bounds result_hessian)
        result_hessian_rows)
Proof
  strip_tac
  >> drule
       compute_registeredCase10173ResultMulContractTheory.registered_case10173_taylor_mul_decimal_source_contract
  >> strip_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173ResultMulContractTheory.registered_case10173_taylor_mul_decimal_contract_components
  >> fs
       [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
  >> fs
       [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_scale_object_shape
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_shape
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawMatrixAddEvalTheory.registered_case10173_fs_raw_interval_matrix_add_object_shape
  >> imp_res_tac registered_case10173_matrix_shape_transfer6
  >> imp_res_tac registered_case10173_matrix_shape6_sum
  >> gvs [listTheory.LENGTH_MAP, listTheory.MAP_MAP_o]
  >> simp
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC [registered_case10173_mul_result_rows_object]
  >> match_mp_tac
       (Q.INST
         [`raw_center_lower:cv` |-> `raw_center_lower`,
          `raw_center_upper:cv` |-> `raw_center_upper`,
          `raw_left_center_gradient:cv list` |-> `raw_left_center_gradient`,
          `raw_right_center_gradient:cv list` |-> `raw_right_center_gradient`,
          `raw_center_gradient:cv list` |-> `raw_center_gradient`,
          `raw_scaled_left_hessian:cv list list` |->
            `raw_scaled_left_hessian`,
          `raw_left_outer_right:cv list list` |-> `raw_left_outer_right`,
          `raw_left_half:cv list list` |-> `raw_left_half`,
          `raw_right_outer_left:cv list list` |-> `raw_right_outer_left`,
          `raw_scaled_right_hessian:cv list list` |->
            `raw_scaled_right_hessian`,
          `raw_right_half:cv list list` |-> `raw_right_half`,
          `raw_hessian_objects:cv list list` |-> `raw_hessian_objects`,
          `result_center_value:bounded_interval64` |-> `result_center`,
          `result_object:cv` |->
            `registered_case10173_mul_result_object_cv
              result_center result_center_gradient result_value
              result_gradient_bounds result_hessian_rows`]
         compute_registeredCase10173ResultMulObjectEvalTheory.registered_case10173_fs_result_mul_object_eval)
  >> asm_rewrite_tac [registered_case10173_mul_result_rows_object]
  >> fs [combinTheory.o_DEF, listTheory.LENGTH_MAP]
  >> fs [listTheory.EVERY_MAP]
  >> CONV_TAC (DEPTH_CONV ETA_CONV)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
