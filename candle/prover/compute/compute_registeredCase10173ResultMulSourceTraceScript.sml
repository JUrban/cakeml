(*****************************************************************************
 * Source-contract trace for the complete Hessian part of Taylor product.
 *
 * This theorem turns the fast compact decimal Hessian result into witnesses
 * for the unchanged historical source program: two full matrix scales, two
 * ordered outer products, three raw matrix additions, and one final outward
 * rounding pass.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulSourceTrace
Ancestors
  compute_registeredCase10173ResultMulFullTrace
  compute_registeredCase10173ResultMulMatrixTrace
  compute_registeredCase10173ResultMulTypedTrace
  compute_registeredCase10173ResultMulObjectEval
Libs
  bossLib preamble

Theorem registered_case10173_fused_hessian_decimal_source_trace:
  bounded_taylor64_well_formed
      (BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian) /\
  bounded_taylor64_well_formed
      (BoundedTaylor64 right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) /\
  bounded_interval64_symmetric_product_pairs
      left_gradient_bounds right_gradient_bounds = SOME outer_pairs /\
  bounded_interval64_fused_hessian_decimal
      left_value right_value left_hessian right_hessian outer_pairs =
    SOME result_hessian ==>
  ?left_hessian_rows right_hessian_rows result_hessian_rows
   raw_scaled_left_hessian raw_left_outer_right raw_left_half
   raw_right_outer_left raw_scaled_right_hessian raw_right_half
   raw_hessian_objects.
    bounded_hessian64_rows left_hessian = SOME left_hessian_rows /\
    bounded_hessian64_rows right_hessian = SOME right_hessian_rows /\
    bounded_hessian64_rows result_hessian = SOME result_hessian_rows /\
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
      SOME (MAP (MAP bounded_interval64_object_cv) result_hessian_rows)
Proof
  strip_tac
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> qpat_x_assum `LENGTH left_hessian = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `left_hessian_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH right_hessian = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `right_hessian_rows` strip_assume_tac)
  >> imp_res_tac
       compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> `LENGTH result_hessian = 21` by fs []
  >> qpat_x_assum `LENGTH result_hessian = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `result_hessian_rows` strip_assume_tac)
  >> drule registered_case10173_fused_hessian_decimal_raw_trace
  >> disch_then
       (qx_choose_then `compact_scaled_left`
         (qx_choose_then `compact_left_outer`
           (qx_choose_then `compact_right_outer`
             (qx_choose_then `compact_scaled_right`
               (qx_choose_then `compact_left_half`
                 (qx_choose_then `compact_right_half`
                   (qx_choose_then `compact_sum` strip_assume_tac)))))))
  >> imp_res_tac
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_length
  >> `LENGTH compact_scaled_left = 21` by fs []
  >> `LENGTH compact_left_outer = 21` by fs []
  >> `LENGTH compact_left_half = 21` by fs []
  >> `LENGTH compact_right_outer = 21` by fs []
  >> `LENGTH compact_scaled_right = 21` by fs []
  >> `LENGTH compact_right_half = 21` by fs []
  >> `LENGTH compact_sum = 21` by fs []
  >> qpat_x_assum `LENGTH compact_scaled_left = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_scaled_left_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH compact_left_outer = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_left_outer_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH compact_left_half = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_left_half_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH compact_right_outer = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_right_outer_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH compact_scaled_right = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_scaled_right_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH compact_right_half = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_right_half_rows` strip_assume_tac)
  >> qpat_x_assum `LENGTH compact_sum = 21`
       (mp_tac o MATCH_MP
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length)
  >> disch_then (qx_choose_then `compact_sum_rows` strip_assume_tac)
  >> mp_tac
       (Q.INST [`scalar` |-> `right_value`]
          (Q.SPEC `left_hessian`
            registered_case10173_raw_list_scale_typed_trace))
  >> disch_then (qx_choose_then `typed_scaled_left` strip_assume_tac)
  >> gvs []
  >> mp_tac
       (Q.INST [`scalar` |-> `left_value`]
          (Q.SPEC `right_hessian`
            registered_case10173_raw_list_scale_typed_trace))
  >> disch_then (qx_choose_then `typed_scaled_right` strip_assume_tac)
  >> gvs []
  >> imp_res_tac registered_case10173_outer_first_trace_relation
  >> imp_res_tac registered_case10173_outer_second_trace_relation
  >> mp_tac
       (Q.INST [`right` |-> `right_gradient_bounds`]
          (Q.SPEC `left_gradient_bounds`
            registered_case10173_raw_outer_typed_trace))
  >> disch_then (qx_choose_then `raw_left_outer_right` strip_assume_tac)
  >> mp_tac
       (Q.INST [`right` |-> `left_gradient_bounds`]
          (Q.SPEC `right_gradient_bounds`
            registered_case10173_raw_outer_typed_trace))
  >> disch_then (qx_choose_then `raw_right_outer_left` strip_assume_tac)
  >> imp_res_tac registered_case10173_raw_product_relation_list_objects
  >> imp_res_tac registered_case10173_raw_product_relation_matrix_objects
  >> imp_res_tac registered_case10173_bounded_hessian64_rows_every
  >> `registered_case10173_raw_outer_matrices_aligned
        compact_left_outer_rows compact_right_outer_rows
        raw_left_outer_right raw_right_outer_left` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `left_gradient_bounds`,
             `right` |-> `right_gradient_bounds`,
             `outer_pairs` |-> `outer_pairs`]
            registered_case10173_raw_outer_source_rows_aligned_length6)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_scale_object
        (bounded_interval64_object_cv right_value)
        (MAP (MAP bounded_interval64_object_cv) left_hessian_rows) =
      SOME compact_scaled_left_rows` by
       (match_mp_tac
          (Q.INST
            [`hessian` |-> `left_hessian`,
             `raw_hessian` |-> `compact_scaled_left`]
            registered_case10173_raw_hessian_scale_rows)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_scale_object
        (bounded_interval64_object_cv left_value)
        (MAP (MAP bounded_interval64_object_cv) right_hessian_rows) =
      SOME compact_scaled_right_rows` by
       (match_mp_tac
          (Q.INST
            [`hessian` |-> `right_hessian`,
             `raw_hessian` |-> `compact_scaled_right`]
            registered_case10173_raw_hessian_scale_rows)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_add_object
        compact_scaled_left_rows compact_left_outer_rows =
      SOME compact_left_half_rows` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `compact_scaled_left`,
             `right` |-> `compact_left_outer`,
             `result` |-> `compact_left_half`]
            registered_case10173_raw_hessian_add_rows)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_add_object
        compact_right_outer_rows compact_scaled_right_rows =
      SOME compact_right_half_rows` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `compact_right_outer`,
             `right` |-> `compact_scaled_right`,
             `result` |-> `compact_right_half`]
            registered_case10173_raw_hessian_add_rows)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_add_object
        compact_left_half_rows compact_right_half_rows =
      SOME compact_sum_rows` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `compact_left_half`,
             `right` |-> `compact_right_half`,
             `result` |-> `compact_sum`]
            registered_case10173_raw_hessian_add_rows)
        >> asm_rewrite_tac [])
  >> imp_res_tac registered_case10173_raw_matrix_add_relation
  >> imp_res_tac registered_case10173_raw_outer_typed_shape6
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> `LIST_REL (\left_row right_row.
        LENGTH left_row = LENGTH right_row)
        compact_scaled_left_rows raw_left_outer_right` by
       (match_mp_tac
          (Q.INST [`width` |-> `6`]
            registered_case10173_equal_width_matrices_list_rel)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
          [`left` |-> `compact_scaled_left_rows`,
           `right` |-> `raw_left_outer_right`]
          registered_case10173_raw_matrix_add_object_trace)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `raw_left_half` strip_assume_tac)
  >> `LIST_REL (\left_row right_row.
        LENGTH left_row = LENGTH right_row)
        raw_right_outer_left compact_scaled_right_rows` by
       (match_mp_tac
          (Q.INST [`width` |-> `6`]
            registered_case10173_equal_width_matrices_list_rel)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
          [`left` |-> `raw_right_outer_left`,
           `right` |-> `compact_scaled_right_rows`]
          registered_case10173_raw_matrix_add_object_trace)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `raw_right_half` strip_assume_tac)
  >> `EVERY (\row. LENGTH row = 6) raw_left_half` by
       (match_mp_tac
          (Q.INST [`width` |-> `6`]
            (Q.SPECL
              [`compact_scaled_left_rows`,`raw_left_outer_right`,
               `raw_left_half`]
              registered_case10173_raw_matrices_add_preserves_width))
        >> asm_rewrite_tac [])
  >> `EVERY (\row. LENGTH row = 6) raw_right_half` by
       (match_mp_tac
          (Q.INST [`width` |-> `6`]
            (Q.SPECL
              [`raw_right_outer_left`,`compact_scaled_right_rows`,
               `raw_right_half`]
              registered_case10173_raw_matrices_add_preserves_width))
        >> asm_rewrite_tac [])
  >> imp_res_tac registered_case10173_raw_matrices_add_lengths
  >> `LENGTH raw_left_half = 6` by fs []
  >> `LENGTH raw_right_half = 6` by fs []
  >> `LIST_REL (\left_row right_row.
        LENGTH left_row = LENGTH right_row)
        raw_left_half raw_right_half` by
       (match_mp_tac
          (Q.INST [`width` |-> `6`]
            registered_case10173_equal_width_matrices_list_rel)
        >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
          [`left` |-> `raw_left_half`,
           `right` |-> `raw_right_half`]
          registered_case10173_raw_matrix_add_object_trace)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `raw_hessian_objects` strip_assume_tac)
  >> `LIST_REL
        (LIST_REL registered_case10173_raw_interval_endpoint_equiv)
        compact_sum_rows raw_hessian_objects` by
       (match_mp_tac
          (Q.SPECL
            [`compact_scaled_left_rows`,`compact_left_outer_rows`,
             `compact_right_outer_rows`,`compact_scaled_right_rows`,
             `compact_left_half_rows`,`compact_right_half_rows`,
             `compact_sum_rows`,`raw_left_outer_right`,
             `raw_right_outer_left`,`raw_left_half`,`raw_right_half`,
             `raw_hessian_objects`]
            registered_case10173_raw_hessian_matrices_endpoint_equiv)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_round_object
        1000000000000 compact_sum_rows =
      SOME (MAP (MAP bounded_interval64_object_cv) result_hessian_rows)` by
       (match_mp_tac
          (Q.INST
            [`raw_hessian` |-> `compact_sum`,
             `rounded_hessian` |-> `result_hessian`]
            registered_case10173_raw_hessian_round_rows)
        >> asm_rewrite_tac [])
  >> `registered_case10173_fs_raw_interval_matrix_round_object
        1000000000000 compact_sum_rows =
      registered_case10173_fs_raw_interval_matrix_round_object
        1000000000000 raw_hessian_objects` by
       (match_mp_tac
          (Q.SPECL [`compact_sum_rows`,`raw_hessian_objects`]
            registered_case10173_raw_matrix_round_endpoint_equiv)
        >> asm_rewrite_tac [])
  >> qexistsl_tac
       [`compact_scaled_left_rows`,`raw_left_outer_right`,`raw_left_half`,
        `raw_right_outer_left`,`compact_scaled_right_rows`,`raw_right_half`,
        `raw_hessian_objects`]
  >> fs []
QED

val _ = export_theory ();
