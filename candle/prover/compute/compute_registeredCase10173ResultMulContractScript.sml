(*****************************************************************************
 * Complete typed-to-source contract for Taylor multiplication.
 *
 * A successful fast decimal multiplication is refined to every raw witness
 * consumed by the unchanged historical [fs_result_mul] source: center value,
 * center gradient, full 6x6 Hessian, and final Taylor completion.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulContract
Ancestors
  compute_registeredCase10173ResultMulSourceTrace
  compute_registeredCase10173ResultMulTypedTrace
Libs
  bossLib preamble

Theorem registered_case10173_taylor_mul_decimal_contract_components:
  bounded_taylor64_mul_decimal radii
      (BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedTaylor64 right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    SOME
      (BoundedTaylor64 result_domain result_center result_center_gradient
        result_value result_gradient_bounds result_hessian) ==>
  bounded_taylor64_well_formed
      (BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian) /\
  bounded_taylor64_well_formed
      (BoundedTaylor64 right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) /\
  bounded_taylor64_complete_decimal radii (left_domain /\ right_domain)
      result_center result_center_gradient result_hessian =
    SOME
      (BoundedTaylor64 result_domain result_center result_center_gradient
        result_value result_gradient_bounds result_hessian)
Proof
  rw [compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_def]
  >> every_case_tac
  >> gvs []
  >> fs
       [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
        LET_THM]
QED

Theorem registered_case10173_taylor_mul_decimal_source_contract:
  bounded_taylor64_mul_decimal radii
      (BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedTaylor64 right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    SOME
      (BoundedTaylor64 result_domain result_center result_center_gradient
        result_value result_gradient_bounds result_hessian) ==>
  ?left_hessian_rows right_hessian_rows result_hessian_rows
   raw_center_lower raw_center_upper
   raw_left_center_gradient raw_right_center_gradient raw_center_gradient
   raw_scaled_left_hessian raw_left_outer_right raw_left_half
   raw_right_outer_left raw_scaled_right_hessian raw_right_half
   raw_hessian_objects.
    bounded_hessian64_rows left_hessian = SOME left_hessian_rows /\
    bounded_hessian64_rows right_hessian = SOME right_hessian_rows /\
    bounded_hessian64_rows result_hessian = SOME result_hessian_rows /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left_center)
        (bounded_interval64_object_cv right_center) =
      SOME (Pair raw_center_lower raw_center_upper) /\
    bounded_object_fs_raw_interval_round 1000000000000
        (Pair raw_center_lower raw_center_upper) =
      SOME (bounded_interval64_object_cv result_center) /\
    registered_case10173_fs_raw_interval_list_scale_object
        (bounded_interval64_object_cv right_center)
        (MAP bounded_interval64_object_cv left_center_gradient) =
      SOME raw_left_center_gradient /\
    registered_case10173_fs_raw_interval_list_scale_object
        (bounded_interval64_object_cv left_center)
        (MAP bounded_interval64_object_cv right_center_gradient) =
      SOME raw_right_center_gradient /\
    registered_case10173_fs_raw_interval_list_add_object
        raw_left_center_gradient raw_right_center_gradient =
      SOME raw_center_gradient /\
    registered_case10173_fs_raw_interval_list_round_object
        1000000000000 raw_center_gradient =
      SOME (MAP bounded_interval64_object_cv result_center_gradient) /\
    registered_case10173_fs_raw_interval_matrix_scale_object
        (bounded_interval64_object_cv right_value)
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
        (bounded_interval64_object_cv left_value)
        (MAP (MAP bounded_interval64_object_cv) right_hessian_rows) =
      SOME raw_scaled_right_hessian /\
    registered_case10173_fs_raw_interval_matrix_add_object
        raw_right_outer_left raw_scaled_right_hessian = SOME raw_right_half /\
    registered_case10173_fs_raw_interval_matrix_add_object
        raw_left_half raw_right_half = SOME raw_hessian_objects /\
    registered_case10173_fs_raw_interval_matrix_round_object
        1000000000000 raw_hessian_objects =
      SOME (MAP (MAP bounded_interval64_object_cv) result_hessian_rows) /\
    bounded_object_fs_taylor_complete radii
        (left_domain /\ right_domain) result_center result_center_gradient
        result_hessian result_hessian_rows =
      SOME
        (bounded_taylor64_rows_object_cv
          (BoundedTaylor64 result_domain result_center result_center_gradient
            result_value result_gradient_bounds result_hessian)
          result_hessian_rows)
Proof
  strip_tac
  >> imp_res_tac
       registered_case10173_taylor_mul_decimal_contract_components
  >> drule registered_case10173_taylor_mul_decimal_center_gradient_trace
  >> disch_then
       (qx_choose_then `raw_center_lower`
         (qx_choose_then `raw_center_upper`
           (qx_choose_then `raw_left_center_gradient`
             (qx_choose_then `raw_right_center_gradient`
               (qx_choose_then `raw_center_gradient`
                 (qx_choose_then `outer_pairs` strip_assume_tac))))))
  >> mp_tac
       (Q.INST
         [`left_domain` |-> `left_domain`,
          `left_center` |-> `left_center`,
          `left_center_gradient` |-> `left_center_gradient`,
          `right_domain` |-> `right_domain`,
          `right_center` |-> `right_center`,
          `right_center_gradient` |-> `right_center_gradient`]
         registered_case10173_fused_hessian_decimal_source_trace)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `left_hessian_rows`
         (qx_choose_then `right_hessian_rows`
           (qx_choose_then `result_hessian_rows`
             (qx_choose_then `raw_scaled_left_hessian`
               (qx_choose_then `raw_left_outer_right`
                 (qx_choose_then `raw_left_half`
                   (qx_choose_then `raw_right_outer_left`
                     (qx_choose_then `raw_scaled_right_hessian`
                       (qx_choose_then `raw_right_half`
                         (qx_choose_then `raw_hessian_objects`
                           strip_assume_tac))))))))))
  >> `bounded_object_fs_taylor_complete radii
        (left_domain /\ right_domain) result_center result_center_gradient
        result_hessian result_hessian_rows =
      SOME
        (bounded_taylor64_rows_object_cv
          (BoundedTaylor64 result_domain result_center result_center_gradient
            result_value result_gradient_bounds result_hessian)
          result_hessian_rows)` by
       (match_mp_tac
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact
        >> asm_rewrite_tac [])
  >> qexistsl_tac
       [`left_hessian_rows`,`right_hessian_rows`,`result_hessian_rows`,
        `raw_center_lower`,`raw_center_upper`,`raw_left_center_gradient`,
        `raw_right_center_gradient`,`raw_center_gradient`,
        `raw_scaled_left_hessian`,`raw_left_outer_right`,`raw_left_half`,
        `raw_right_outer_left`,`raw_scaled_right_hessian`,`raw_right_half`,
        `raw_hessian_objects`]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
