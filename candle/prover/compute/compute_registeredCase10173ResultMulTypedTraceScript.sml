(*****************************************************************************
 * Typed decimal witnesses for the historical Taylor product trace.
 *
 * The fast checker fuses products before its one outward decimal rounding.
 * The authenticated source first builds explicit unrounded object products
 * and sums, then rounds.  These lemmas construct the source witnesses and
 * prove that the two staging choices meet at exactly the same rounded value.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulTypedTrace
Ancestors
  compute_registeredCase10173ResultMulObjectEval
  compute_registeredCase10173HistoricalDeltaGradientBlockEval
  compute_boundedTaylorMulDecimal
Libs
  bossLib preamble intLib

Theorem registered_case10173_mul_decimal_raw_trace:
  bounded_interval64_mul_decimal left right = SOME result ==>
  ?raw_lower raw_upper.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left)
        (bounded_interval64_object_cv right) =
      SOME (Pair raw_lower raw_upper) /\
    bounded_object_fs_raw_interval_round 1000000000000
        (Pair raw_lower raw_upper) =
      SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> drule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> rw
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_def]
  >> every_case_tac
  >> gvs []
  >> Cases_on `x`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
QED

Theorem registered_case10173_two_raw_products_add_round_fused_exact:
  bounded_interval64_fused_products_decimal
      [(left0,right0);(left1,right1)] = SOME result ==>
  ?raw0 raw1 raw_sum.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left0)
        (bounded_interval64_object_cv right0) = SOME raw0 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left1)
        (bounded_interval64_object_cv right1) = SOME raw1 /\
    bounded_object_fs_raw_interval_add raw0 raw1 = SOME raw_sum /\
    bounded_object_fs_raw_interval_round 1000000000000 raw_sum =
      SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL [`left0`,`right0`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `raw0` assume_tac)
  >> mp_tac
       (Q.SPECL [`left1`,`right1`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `raw1` assume_tac)
  >> mp_tac
       (Q.SPECL [`left0`,`right0`,`raw0`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values)
  >> impl_tac >- simp []
  >> strip_tac
  >> mp_tac
       (Q.SPECL [`left1`,`right1`,`raw1`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values)
  >> impl_tac >- simp []
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`raw0`,`raw1`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left0 right0)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left0 right0)`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left1 right1)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left1 right1)`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_sum` strip_assume_tac)
  >> drule
       compute_boundedObjectDecimalFusedTheory.bounded_object_fs_fused_products_decimal_object_exact
  >> disch_then
       (qx_choose_then `compact_lower`
         (qx_choose_then `compact_upper` strip_assume_tac))
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_products_endpoint_values
  >> qexists_tac `raw0`
  >> qexists_tac `raw1`
  >> qexists_tac `raw_sum`
  >> simp []
  >> `bounded_object_fs_raw_interval_round 1000000000000 raw_sum =
      bounded_object_fs_raw_interval_round 1000000000000
        (Pair compact_lower compact_upper)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_round_ints_extensional
        >> simp
             [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
              LET_THM]
        >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem registered_case10173_raw_product_trace:
  !left right.
    ?raw.
      bounded_object_fs_raw_interval_mul
          (bounded_interval64_object_cv left)
          (bounded_interval64_object_cv right) = SOME raw /\
      bounded_object_interval_ints raw =
        SOME
          (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
            left right)
Proof
  rpt gen_tac
  >> mp_tac
       (Q.SPECL [`left`,`right`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `raw` assume_tac)
  >> qexists_tac `raw`
  >> simp []
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> simp []
QED

Theorem registered_case10173_four_raw_products_tree_round_fused_exact:
  bounded_interval64_fused_products_decimal
      [(left0,right0);(left1,right1);(left2,right2);(left3,right3)] =
    SOME result ==>
  ?raw0 raw1 raw2 raw3 raw_left raw_right raw_sum.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left0)
        (bounded_interval64_object_cv right0) = SOME raw0 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left1)
        (bounded_interval64_object_cv right1) = SOME raw1 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left2)
        (bounded_interval64_object_cv right2) = SOME raw2 /\
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left3)
        (bounded_interval64_object_cv right3) = SOME raw3 /\
    bounded_object_fs_raw_interval_add raw0 raw1 = SOME raw_left /\
    bounded_object_fs_raw_interval_add raw2 raw3 = SOME raw_right /\
    bounded_object_fs_raw_interval_add raw_left raw_right = SOME raw_sum /\
    bounded_object_fs_raw_interval_round 1000000000000 raw_sum =
      SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac (Q.SPECL [`left0`,`right0`] registered_case10173_raw_product_trace)
  >> disch_then (qx_choose_then `raw0` strip_assume_tac)
  >> mp_tac (Q.SPECL [`left1`,`right1`] registered_case10173_raw_product_trace)
  >> disch_then (qx_choose_then `raw1` strip_assume_tac)
  >> mp_tac (Q.SPECL [`left2`,`right2`] registered_case10173_raw_product_trace)
  >> disch_then (qx_choose_then `raw2` strip_assume_tac)
  >> mp_tac (Q.SPECL [`left3`,`right3`] registered_case10173_raw_product_trace)
  >> disch_then (qx_choose_then `raw3` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`raw0`,`raw1`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left0 right0)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left0 right0)`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left1 right1)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left1 right1)`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_left` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`raw2`,`raw3`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left2 right2)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left2 right2)`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left3 right3)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left3 right3)`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_right` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`raw_left`,`raw_right`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left0 right0) +
           FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left1 right1)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left0 right0) +
           SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left1 right1)`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left2 right2) +
           FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left3 right3)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left2 right2) +
           SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left3 right3)`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_sum` strip_assume_tac)
  >> drule
       compute_boundedObjectDecimalFusedTheory.bounded_object_fs_fused_products_decimal_object_exact
  >> disch_then
       (qx_choose_then `compact_lower`
         (qx_choose_then `compact_upper` strip_assume_tac))
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_products_endpoint_values
  >> qexists_tac `raw0`
  >> qexists_tac `raw1`
  >> qexists_tac `raw2`
  >> qexists_tac `raw3`
  >> qexists_tac `raw_left`
  >> qexists_tac `raw_right`
  >> qexists_tac `raw_sum`
  >> simp []
  >> `bounded_object_fs_raw_interval_round 1000000000000 raw_sum =
      bounded_object_fs_raw_interval_round 1000000000000
        (Pair compact_lower compact_upper)` by
       (irule
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_round_ints_extensional
        >> simp
             [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
              LET_THM]
        >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem registered_case10173_fused_scale_add_decimal_raw_trace:
  !left right result.
    bounded_interval64_fused_scale_add_decimal
        left_scale left right_scale right = SOME result ==>
    ?raw_left raw_right raw_sum.
      registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv left_scale)
          (MAP bounded_interval64_object_cv left) = SOME raw_left /\
      registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv right_scale)
          (MAP bounded_interval64_object_cv right) = SOME raw_right /\
      registered_case10173_fs_raw_interval_list_add_object
          raw_left raw_right = SOME raw_sum /\
      registered_case10173_fs_raw_interval_list_round_object
          1000000000000 raw_sum =
        SOME (MAP bounded_interval64_object_cv result)
Proof
  Induct
  >- (Cases_on `right`
      >> simp
           [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_scale_add_decimal_def,
            compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
            compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_def,
            compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def])
  >> gen_tac
  >> Cases_on `right`
  >- simp
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_scale_add_decimal_def]
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_scale_add_decimal_def]
  >> every_case_tac
  >> gvs []
  >> qpat_x_assum `!right result. _`
       (mp_tac o Q.SPECL [`t`,`x`])
  >> simp []
  >> disch_then
       (qx_choose_then `raw_left_tail`
         (qx_choose_then `raw_right_tail`
           (qx_choose_then `raw_sum_tail` strip_assume_tac)))
  >> drule registered_case10173_two_raw_products_add_round_fused_exact
  >> disch_then
       (qx_choose_then `raw_left_head`
         (qx_choose_then `raw_right_head`
           (qx_choose_then `raw_sum_head` strip_assume_tac)))
  >> qexists_tac `raw_left_head::raw_left_tail`
  >> qexists_tac `raw_right_head::raw_right_tail`
  >> qexists_tac `raw_sum_head::raw_sum_tail`
  >> simp
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
        compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def]
QED

Theorem registered_case10173_taylor_mul_decimal_components:
  bounded_taylor64_mul_decimal radii
      (BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedTaylor64 right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    SOME
      (BoundedTaylor64 result_domain result_center result_center_gradient
        result_value result_gradient_bounds result_hessian) ==>
  bounded_interval64_mul_decimal left_center right_center =
      SOME result_center /\
  bounded_interval64_fused_scale_add_decimal
      right_center left_center_gradient
      left_center right_center_gradient = SOME result_center_gradient /\
  ?outer_pairs.
    bounded_interval64_symmetric_product_pairs
        left_gradient_bounds right_gradient_bounds = SOME outer_pairs /\
    bounded_interval64_fused_hessian_decimal
        left_value right_value left_hessian right_hessian outer_pairs =
      SOME result_hessian
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

Theorem registered_case10173_taylor_mul_decimal_center_gradient_trace:
  bounded_taylor64_mul_decimal radii
      (BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedTaylor64 right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    SOME
      (BoundedTaylor64 result_domain result_center result_center_gradient
        result_value result_gradient_bounds result_hessian) ==>
  ?raw_center_lower raw_center_upper raw_left_gradient raw_right_gradient
     raw_center_gradient outer_pairs.
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
      SOME raw_left_gradient /\
    registered_case10173_fs_raw_interval_list_scale_object
        (bounded_interval64_object_cv left_center)
        (MAP bounded_interval64_object_cv right_center_gradient) =
      SOME raw_right_gradient /\
    registered_case10173_fs_raw_interval_list_add_object
        raw_left_gradient raw_right_gradient = SOME raw_center_gradient /\
    registered_case10173_fs_raw_interval_list_round_object
        1000000000000 raw_center_gradient =
      SOME (MAP bounded_interval64_object_cv result_center_gradient) /\
    bounded_interval64_symmetric_product_pairs
        left_gradient_bounds right_gradient_bounds = SOME outer_pairs /\
    bounded_interval64_fused_hessian_decimal
        left_value right_value left_hessian right_hessian outer_pairs =
      SOME result_hessian
Proof
  strip_tac
  >> imp_res_tac registered_case10173_taylor_mul_decimal_components
  >> imp_res_tac registered_case10173_mul_decimal_raw_trace
  >> imp_res_tac registered_case10173_fused_scale_add_decimal_raw_trace
  >> metis_tac []
QED

Theorem registered_case10173_fused_hessian_decimal_raw_trace:
  !left_hessian right_hessian outer_pairs result_hessian.
    bounded_interval64_fused_hessian_decimal
        left_value right_value left_hessian right_hessian outer_pairs =
      SOME result_hessian ==>
    ?raw_scaled_left raw_left_outer_right raw_right_outer_left
       raw_scaled_right raw_left_half raw_right_half raw_hessian.
      registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv right_value)
          (MAP bounded_interval64_object_cv left_hessian) =
        SOME raw_scaled_left /\
      LIST_REL
        (\outer raw.
           bounded_object_fs_raw_interval_mul
             (bounded_interval64_object_cv (FST (FST outer)))
             (bounded_interval64_object_cv (SND (FST outer))) = SOME raw)
        outer_pairs raw_left_outer_right /\
      LIST_REL
        (\outer raw.
           bounded_object_fs_raw_interval_mul
             (bounded_interval64_object_cv (FST (SND outer)))
             (bounded_interval64_object_cv (SND (SND outer))) = SOME raw)
        outer_pairs raw_right_outer_left /\
      registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv left_value)
          (MAP bounded_interval64_object_cv right_hessian) =
        SOME raw_scaled_right /\
      registered_case10173_fs_raw_interval_list_add_object
          raw_scaled_left raw_left_outer_right = SOME raw_left_half /\
      registered_case10173_fs_raw_interval_list_add_object
          raw_right_outer_left raw_scaled_right = SOME raw_right_half /\
      registered_case10173_fs_raw_interval_list_add_object
          raw_left_half raw_right_half = SOME raw_hessian /\
      registered_case10173_fs_raw_interval_list_round_object
          1000000000000 raw_hessian =
        SOME (MAP bounded_interval64_object_cv result_hessian)
Proof
  Induct_on `left_hessian`
  >- (Cases_on `right_hessian`
      >> Cases_on `outer_pairs`
      >> simp
           [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def,
            compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
            compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_def,
            compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def])
  >> rpt gen_tac
  >> Cases_on `right_hessian`
  >- (Cases_on `outer_pairs`
      >> fs
           [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def])
  >> Cases_on `outer_pairs`
  >- fs
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def]
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def]
  >> every_case_tac
  >> gvs []
  >> qpat_x_assum `!right_hessian outer_pairs result_hessian. _`
       (mp_tac o Q.SPECL [`t`,`t'`,`x`])
  >> impl_tac >- simp []
  >> disch_then
       (qx_choose_then `raw_scaled_left_tail`
         (qx_choose_then `raw_left_outer_right_tail`
           (qx_choose_then `raw_right_outer_left_tail`
             (qx_choose_then `raw_scaled_right_tail`
               (qx_choose_then `raw_left_half_tail`
                 (qx_choose_then `raw_right_half_tail`
                   (qx_choose_then `raw_hessian_tail` strip_assume_tac)))))))
  >> PairCases_on `h''`
  >> gvs []
  >> drule registered_case10173_four_raw_products_tree_round_fused_exact
  >> disch_then
       (qx_choose_then `raw_scaled_left_head`
         (qx_choose_then `raw_left_outer_right_head`
           (qx_choose_then `raw_right_outer_left_head`
             (qx_choose_then `raw_scaled_right_head`
               (qx_choose_then `raw_left_half_head`
                 (qx_choose_then `raw_right_half_head`
                   (qx_choose_then `raw_hessian_head` strip_assume_tac)))))))
  >> qexists_tac `raw_scaled_left_head::raw_scaled_left_tail`
  >> qexists_tac `raw_left_outer_right_head::raw_left_outer_right_tail`
  >> qexists_tac `raw_right_outer_left_head::raw_right_outer_left_tail`
  >> qexists_tac `raw_scaled_right_head::raw_scaled_right_tail`
  >> qexists_tac `raw_left_half_head::raw_left_half_tail`
  >> qexists_tac `raw_right_half_head::raw_right_half_tail`
  >> qexists_tac `raw_hessian_head::raw_hessian_tail`
  >> simp
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
        compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def,
        LIST_REL_def]
QED

val _ = export_theory ();
