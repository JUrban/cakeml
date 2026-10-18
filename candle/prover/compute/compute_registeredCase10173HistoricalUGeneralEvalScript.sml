(*****************************************************************************
 * Packet-independent evaluator refinement for the historical u126/u135
 * first-order components.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUGeneralEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4GeneralEval
  compute_registeredCase10173HistoricalDeltaX4ValueBlockEval
  compute_registeredCase10173HistoricalDeltaGradientBlockEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_interval_scale_two_object_ints_general:
  !source lower upper.
    bounded_object_interval_ints source = SOME (lower,upper) ==>
    ?result.
      registered_case10173_fs_interval_raw_scale_object 2 source =
        SOME result /\
      bounded_object_interval_ints result = SOME (2 * lower,2 * upper)
Proof
  rpt gen_tac
  >> Cases_on `source`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> strip_tac
  >> mp_tac
       (Q.INST [`source` |-> `c`, `value` |-> `lower`, `factor` |-> `2`]
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_signed_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `scaled_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST [`source` |-> `c0`, `value` |-> `upper`, `factor` |-> `2`]
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_signed_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `scaled_upper` strip_assume_tac)
  >> qexists_tac `Pair scaled_lower scaled_upper`
  >> simp
       [compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
QED

Theorem bounded_signed64_normalized_to_int_injective:
  !left right.
    bounded_signed64_normalized left /\
    bounded_signed64_normalized right /\
    bounded_signed64_to_int left = bounded_signed64_to_int right ==>
    left = right
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        wordsTheory.w2n_eq_0]
  >> metis_tac [wordsTheory.w2n_11]
QED

Theorem bounded_interval64_sum_three_inputs_valid:
  !left middle right result.
    bounded_interval64_sum [left;middle;right] = SOME result ==>
    bounded_interval64_valid left /\
    bounded_interval64_valid middle /\
    bounded_interval64_valid right
Proof
  rpt gen_tac
  >> rw
       [compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def,
        compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def]
  >> every_case_tac
  >> gvs [compute_boundedIntervalAddTheory.bounded_interval64_add_def]
QED

Theorem bounded_interval64_sum_three_endpoint_values:
  !left middle right result.
    bounded_interval64_sum [left;middle;right] = SOME result ==>
    bounded_signed64_to_int (bounded_interval64_lower result) =
      bounded_signed64_to_int (bounded_interval64_lower left) +
      bounded_signed64_to_int (bounded_interval64_lower middle) +
      bounded_signed64_to_int (bounded_interval64_lower right) /\
    bounded_signed64_to_int (bounded_interval64_upper result) =
      bounded_signed64_to_int (bounded_interval64_upper left) +
      bounded_signed64_to_int (bounded_interval64_upper middle) +
      bounded_signed64_to_int (bounded_interval64_upper right)
Proof
  rpt gen_tac
  >> strip_tac
  >> mp_tac
       (Q.INST [`values` |-> `[left;middle;right]`, `result` |-> `result`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_interval64_sum_endpoint_values)
  >> impl_tac >- simp []
  >> fs
       [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_valid_endpoint_components:
  !interval.
    bounded_interval64_valid interval ==>
    bounded_signed64_normalized (bounded_interval64_lower interval) /\
    bounded_signed64_normalized (bounded_interval64_upper interval) /\
    bounded_signed64_to_int (bounded_interval64_lower interval) <=
      bounded_signed64_to_int (bounded_interval64_upper interval)
Proof
  Cases_on `interval`
  >> simp
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_historical_scaled_sum_zero_tie_degenerate:
  !left middle right half gradient.
    bounded_interval64_sum [left;middle;right] = SOME half /\
    bounded_historical_scale2 half = SOME gradient /\
    bounded_signed64_nonnegative (bounded_interval64_lower gradient) /\
    bounded_signed64_nonpositive (bounded_interval64_upper gradient) ==>
    bounded_interval64_lower left = bounded_interval64_upper left /\
    bounded_interval64_lower middle = bounded_interval64_upper middle /\
    bounded_interval64_lower right = bounded_interval64_upper right
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac bounded_interval64_sum_three_inputs_valid
  >> imp_res_tac bounded_interval64_sum_three_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_interval64_sum_valid
  >> imp_res_tac bounded_interval64_valid_endpoint_components
  >> fs
       [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def]
  >> imp_res_tac compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
  >> `bounded_signed64_to_int (bounded_interval64_lower left) =
        bounded_signed64_to_int (bounded_interval64_upper left) /\
      bounded_signed64_to_int (bounded_interval64_lower middle) =
        bounded_signed64_to_int (bounded_interval64_upper middle) /\
      bounded_signed64_to_int (bounded_interval64_lower right) =
        bounded_signed64_to_int (bounded_interval64_upper right)` by
       intLib.ARITH_TAC
  >> metis_tac [bounded_signed64_normalized_to_int_injective]
QED

Theorem bounded_historical_scaled_sum_tie_or_degenerate:
  !left middle right half gradient.
    bounded_interval64_sum [left;middle;right] = SOME half /\
    bounded_historical_scale2 half = SOME gradient ==>
    ~(bounded_signed64_nonnegative (bounded_interval64_lower gradient) /\
      bounded_signed64_nonpositive (bounded_interval64_upper gradient)) \/
    (bounded_interval64_lower left = bounded_interval64_upper left /\
     bounded_interval64_lower middle = bounded_interval64_upper middle /\
     bounded_interval64_lower right = bounded_interval64_upper right)
Proof
  rpt gen_tac
  >> strip_tac
  >> Cases_on
       `bounded_signed64_nonnegative (bounded_interval64_lower gradient) /\
        bounded_signed64_nonpositive (bounded_interval64_upper gradient)`
  >> simp []
  >> metis_tac [bounded_historical_scaled_sum_zero_tie_degenerate]
QED

Theorem bounded_interval64_neg_degenerate_source:
  !value.
    bounded_interval64_valid value /\
    bounded_interval64_lower (bounded_interval64_neg value) =
      bounded_interval64_upper (bounded_interval64_neg value) ==>
    bounded_interval64_lower value = bounded_interval64_upper value
Proof
  rpt gen_tac
  >> strip_tac
  >> imp_res_tac bounded_interval64_valid_endpoint_components
  >> mp_tac
       (Q.INST [`source` |-> `value`]
          compute_boundedIntervalAddTheory.bounded_interval64_neg_value)
  >> strip_tac
  >> `bounded_signed64_to_int
        (bounded_interval64_lower (bounded_interval64_neg value)) =
      bounded_signed64_to_int
        (bounded_interval64_upper (bounded_interval64_neg value))` by
       metis_tac []
  >> `bounded_signed64_to_int (bounded_interval64_lower value) =
        bounded_signed64_to_int (bounded_interval64_upper value)` by
       intLib.ARITH_TAC
  >> metis_tac [bounded_signed64_normalized_to_int_injective]
QED

Theorem registered_case10173_historical_u_point_elements_source_selectors:
  !(value:bounded_interval64) gradient.
    (~(bounded_signed64_nonnegative (bounded_interval64_lower gradient) /\
       bounded_signed64_nonpositive (bounded_interval64_upper gradient)) \/
     bounded_interval64_lower value = bounded_interval64_upper value) ==>
    let points =
          registered_case10173_fs_hist_u_point_elements
            (bounded_signed64_object_cv (bounded_interval64_lower value))
            (bounded_signed64_object_cv (bounded_interval64_upper value))
            (bounded_signed64_nonnegative
              (bounded_interval64_lower gradient))
            (bounded_signed64_nonpositive
              (bounded_interval64_upper gradient))
    in
      EL 0 points =
        bounded_interval64_object_cv
          (bounded_historical_u_upper_negative value gradient) /\
      EL 1 points =
        bounded_interval64_object_cv
          (bounded_historical_u_upper_positive value gradient) /\
      EL 2 points =
        bounded_interval64_object_cv
          (bounded_historical_u_lower_negative value gradient) /\
      EL 3 points =
        bounded_interval64_object_cv
          (bounded_historical_u_lower_positive value gradient)
Proof
  rpt gen_tac
  >> Cases_on
       `bounded_signed64_nonnegative (bounded_interval64_lower gradient)`
  >> Cases_on
       `bounded_signed64_nonpositive (bounded_interval64_upper gradient)`
  >> Cases_on `value`
  >> fs
       [compute_registeredCase10173HistoricalUThreeEvalTheory.registered_case10173_fs_hist_u_point_elements_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_negative_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_positive_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_negative_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_positive_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        LET_THM]
QED

Theorem registered_case10173_historical_u_point_elements_source_list:
  !(value:bounded_interval64) gradient.
    (~(bounded_signed64_nonnegative (bounded_interval64_lower gradient) /\
       bounded_signed64_nonpositive (bounded_interval64_upper gradient)) \/
     bounded_interval64_lower value = bounded_interval64_upper value) ==>
    registered_case10173_fs_hist_u_point_elements
      (bounded_signed64_object_cv (bounded_interval64_lower value))
      (bounded_signed64_object_cv (bounded_interval64_upper value))
      (bounded_signed64_nonnegative (bounded_interval64_lower gradient))
      (bounded_signed64_nonpositive (bounded_interval64_upper gradient)) =
    [bounded_interval64_object_cv
       (bounded_historical_u_upper_negative value gradient);
     bounded_interval64_object_cv
       (bounded_historical_u_upper_positive value gradient);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_negative value gradient);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_positive value gradient)]
Proof
  rpt gen_tac
  >> Cases_on
       `bounded_signed64_nonnegative (bounded_interval64_lower gradient)`
  >> Cases_on
       `bounded_signed64_nonpositive (bounded_interval64_upper gradient)`
  >> Cases_on `value`
  >> fs
       [compute_registeredCase10173HistoricalUThreeEvalTheory.registered_case10173_fs_hist_u_point_elements_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_negative_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_positive_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_negative_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_positive_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
        compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem registered_case10173_historical_u_three_point_elements_source_lists:
  bounded_interval64_sum [bounded_interval64_neg x0;x1;x2] = SOME g0_half /\
  bounded_historical_scale2 g0_half = SOME g0 /\
  bounded_interval64_sum [x0;bounded_interval64_neg x1;x2] = SOME g1_half /\
  bounded_historical_scale2 g1_half = SOME g1 /\
  bounded_interval64_sum [x0;x1;bounded_interval64_neg x2] = SOME g2_half /\
  bounded_historical_scale2 g2_half = SOME g2 ==>
  registered_case10173_fs_hist_u_point_elements
      (bounded_signed64_object_cv (bounded_interval64_lower x0))
      (bounded_signed64_object_cv (bounded_interval64_upper x0))
      (bounded_signed64_nonnegative (bounded_interval64_lower g0))
      (bounded_signed64_nonpositive (bounded_interval64_upper g0)) =
    [bounded_interval64_object_cv
       (bounded_historical_u_upper_negative x0 g0);
     bounded_interval64_object_cv
       (bounded_historical_u_upper_positive x0 g0);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_negative x0 g0);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_positive x0 g0)] /\
  registered_case10173_fs_hist_u_point_elements
      (bounded_signed64_object_cv (bounded_interval64_lower x1))
      (bounded_signed64_object_cv (bounded_interval64_upper x1))
      (bounded_signed64_nonnegative (bounded_interval64_lower g1))
      (bounded_signed64_nonpositive (bounded_interval64_upper g1)) =
    [bounded_interval64_object_cv
       (bounded_historical_u_upper_negative x1 g1);
     bounded_interval64_object_cv
       (bounded_historical_u_upper_positive x1 g1);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_negative x1 g1);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_positive x1 g1)] /\
  registered_case10173_fs_hist_u_point_elements
      (bounded_signed64_object_cv (bounded_interval64_lower x2))
      (bounded_signed64_object_cv (bounded_interval64_upper x2))
      (bounded_signed64_nonnegative (bounded_interval64_lower g2))
      (bounded_signed64_nonpositive (bounded_interval64_upper g2)) =
    [bounded_interval64_object_cv
       (bounded_historical_u_upper_negative x2 g2);
     bounded_interval64_object_cv
       (bounded_historical_u_upper_positive x2 g2);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_negative x2 g2);
     bounded_interval64_object_cv
       (bounded_historical_u_lower_positive x2 g2)]
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_sum_three_inputs_valid
  >> mp_tac
       (Q.SPECL
         [`bounded_interval64_neg x0`,`x1`,`x2`,`g0_half`,`g0`]
         bounded_historical_scaled_sum_tie_or_degenerate)
  >> impl_tac >- simp []
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`x0`,`bounded_interval64_neg x1`,`x2`,`g1_half`,`g1`]
         bounded_historical_scaled_sum_tie_or_degenerate)
  >> impl_tac >- simp []
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`x0`,`x1`,`bounded_interval64_neg x2`,`g2_half`,`g2`]
         bounded_historical_scaled_sum_tie_or_degenerate)
  >> impl_tac >- simp []
  >> strip_tac
  >> `~(bounded_signed64_nonnegative (bounded_interval64_lower g0) /\
         bounded_signed64_nonpositive (bounded_interval64_upper g0)) \/
      bounded_interval64_lower x0 = bounded_interval64_upper x0` by
       metis_tac [bounded_interval64_neg_degenerate_source]
  >> `~(bounded_signed64_nonnegative (bounded_interval64_lower g1) /\
         bounded_signed64_nonpositive (bounded_interval64_upper g1)) \/
      bounded_interval64_lower x1 = bounded_interval64_upper x1` by
       metis_tac [bounded_interval64_neg_degenerate_source]
  >> `~(bounded_signed64_nonnegative (bounded_interval64_lower g2) /\
         bounded_signed64_nonpositive (bounded_interval64_upper g2)) \/
      bounded_interval64_lower x2 = bounded_interval64_upper x2` by
       metis_tac [bounded_interval64_neg_degenerate_source]
  >> metis_tac
       [registered_case10173_historical_u_point_elements_source_list]
QED

Theorem registered_case10173_historical_u_value_formula_block_typed_exact:
  selector + 1 < LENGTH points0 /\
  selector + 1 < LENGTH points1 /\
  selector + 1 < LENGTH points2 /\
  EL selector points0 = bounded_interval64_object_cv n0 /\
  EL selector points1 = bounded_interval64_object_cv n1 /\
  EL selector points2 = bounded_interval64_object_cv n2 /\
  EL (selector + 1) points0 = bounded_interval64_object_cv p0 /\
  EL (selector + 1) points1 = bounded_interval64_object_cv p1 /\
  EL (selector + 1) points2 = bounded_interval64_object_cv p2 /\
  bounded_historical_u_block_decimal n0 n1 n2 p0 p1 p2 =
    SOME result ==>
  registered_case10173_fs_hist_u_value_formula_object selector
      points0 points1 points2 =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> fs
       [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u_block_decimal_def]
  >> mp_tac
       (Q.SPECL [`n0`,`n0`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then `n0_square`
         (qx_choose_then `negative_n0_square` strip_assume_tac))
  >> mp_tac
       (Q.SPECL [`n1`,`n1`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then `n1_square`
         (qx_choose_then `negative_n1_square` strip_assume_tac))
  >> mp_tac
       (Q.SPECL [`n2`,`n2`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then `n2_square`
         (qx_choose_then `negative_n2_square` strip_assume_tac))
  >> mp_tac
       (Q.SPECL [`p0`,`p1`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p01` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`p1`,`p2`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p12` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`p2`,`p0`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p20` strip_assume_tac)
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> mp_tac
       (Q.SPECL
         [`p01`,
          `FST
            (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
              p0 p1)`,
          `SND
            (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
              p0 p1)`]
         registered_case10173_interval_scale_two_object_ints_general)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `twice_p01` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`p12`,
          `FST
            (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
              p1 p2)`,
          `SND
            (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
              p1 p2)`]
         registered_case10173_interval_scale_two_object_ints_general)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `twice_p12` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`p20`,
          `FST
            (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
              p2 p0)`,
          `SND
            (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
              p2 p0)`]
         registered_case10173_interval_scale_two_object_ints_general)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `twice_p20` strip_assume_tac)
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [negative_n0_square;negative_n1_square;negative_n2_square;
         twice_p01;twice_p12;twice_p20] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(bounded_interval64_neg n0,n0);
           (bounded_interval64_neg n1,n1);
           (bounded_interval64_neg n2,n2);
           (p0,p1);(p0,p1);(p1,p2);(p1,p2);(p2,p0);(p2,p0)])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_raw_product_ints_negated_left,
           LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                p0 p1`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                p1 p2`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                p2 p0`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaGradientBlockEvalTheory.registered_case10173_source_raw_sum_round_fused_exact
  >> fs
       [compute_registeredCase10173HistoricalUValueObjectEvalTheory.registered_case10173_fs_hist_u_value_formula_object_def]
QED

Theorem bounded_object_fs_raw_le_zero_signed_object_cv:
  bounded_object_fs_raw_le (Pair (Num 0) (Num 0))
      (bounded_signed64_object_cv value) =
    SOME (bounded_signed64_nonnegative value)
Proof
  `(Pair (Num 0) (Num 0):cv) =
      bounded_signed64_object_cv (BoundedSigned64 F 0w)` by
    simp
      [compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> pop_assum SUBST1_TAC
  >> simp
       [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_object_cv,
        compute_boundedObjectHistoricalSecondDecimalTheory.bounded_signed64_zero_le_iff_nonnegative]
QED

Theorem bounded_object_fs_raw_le_signed_object_cv_zero:
  bounded_object_fs_raw_le (bounded_signed64_object_cv value)
      (Pair (Num 0) (Num 0)) =
    SOME (bounded_signed64_nonpositive value)
Proof
  `(Pair (Num 0) (Num 0):cv) =
      bounded_signed64_object_cv (BoundedSigned64 F 0w)` by
    simp
      [compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> pop_assum SUBST1_TAC
  >> simp
       [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_object_cv,
        compute_boundedObjectHistoricalSecondDecimalTheory.bounded_signed64_le_zero_iff_nonpositive]
QED

Theorem registered_case10173_historical_u_after_gradients_object_typed_exact:
  bounded_interval64_sum [bounded_interval64_neg x0;x1;x2] = SOME g0_half /\
  bounded_historical_scale2 g0_half = SOME g0 /\
  bounded_interval64_sum [x0;bounded_interval64_neg x1;x2] = SOME g1_half /\
  bounded_historical_scale2 g1_half = SOME g1 /\
  bounded_interval64_sum [x0;x1;bounded_interval64_neg x2] = SOME g2_half /\
  bounded_historical_scale2 g2_half = SOME g2 /\
  bounded_historical_u_block_decimal
      (bounded_historical_u_lower_negative x0 g0)
      (bounded_historical_u_lower_negative x1 g1)
      (bounded_historical_u_lower_negative x2 g2)
      (bounded_historical_u_lower_positive x0 g0)
      (bounded_historical_u_lower_positive x1 g1)
      (bounded_historical_u_lower_positive x2 g2) = SOME lower_value /\
  bounded_historical_u_block_decimal
      (bounded_historical_u_upper_negative x0 g0)
      (bounded_historical_u_upper_negative x1 g1)
      (bounded_historical_u_upper_negative x2 g2)
      (bounded_historical_u_upper_positive x0 g0)
      (bounded_historical_u_upper_positive x1 g1)
      (bounded_historical_u_upper_positive x2 g2) = SOME upper_value ==>
  registered_case10173_fs_hist_u_after_gradients_object
      (bounded_interval64_object_cv x0)
      (bounded_interval64_object_cv x1)
      (bounded_interval64_object_cv x2)
      (bounded_interval64_object_cv g0)
      (bounded_interval64_object_cv g1)
      (bounded_interval64_object_cv g2) =
    SOME
      (Pair
        (bounded_interval64_object_cv
          (BoundedInterval64
            (bounded_interval64_lower lower_value)
            (bounded_interval64_upper upper_value)))
        (bounded_interval64_object_cv_list [g0;g1;g2]))
Proof
  strip_tac
  >> mp_tac
       registered_case10173_historical_u_three_point_elements_source_lists
  >> impl_tac >- simp []
  >> strip_tac
  >> `registered_case10173_fs_hist_u_value_formula_object 2
        (registered_case10173_fs_hist_u_point_elements
          (bounded_signed64_object_cv (bounded_interval64_lower x0))
          (bounded_signed64_object_cv (bounded_interval64_upper x0))
          (bounded_signed64_nonnegative (bounded_interval64_lower g0))
          (bounded_signed64_nonpositive (bounded_interval64_upper g0)))
        (registered_case10173_fs_hist_u_point_elements
          (bounded_signed64_object_cv (bounded_interval64_lower x1))
          (bounded_signed64_object_cv (bounded_interval64_upper x1))
          (bounded_signed64_nonnegative (bounded_interval64_lower g1))
          (bounded_signed64_nonpositive (bounded_interval64_upper g1)))
        (registered_case10173_fs_hist_u_point_elements
          (bounded_signed64_object_cv (bounded_interval64_lower x2))
          (bounded_signed64_object_cv (bounded_interval64_upper x2))
          (bounded_signed64_nonnegative (bounded_interval64_lower g2))
          (bounded_signed64_nonpositive (bounded_interval64_upper g2))) =
      SOME (bounded_interval64_object_cv lower_value)` by
       (irule registered_case10173_historical_u_value_formula_block_typed_exact
        >> simp []
        >> metis_tac [])
  >> `registered_case10173_fs_hist_u_value_formula_object 0
        (registered_case10173_fs_hist_u_point_elements
          (bounded_signed64_object_cv (bounded_interval64_lower x0))
          (bounded_signed64_object_cv (bounded_interval64_upper x0))
          (bounded_signed64_nonnegative (bounded_interval64_lower g0))
          (bounded_signed64_nonpositive (bounded_interval64_upper g0)))
        (registered_case10173_fs_hist_u_point_elements
          (bounded_signed64_object_cv (bounded_interval64_lower x1))
          (bounded_signed64_object_cv (bounded_interval64_upper x1))
          (bounded_signed64_nonnegative (bounded_interval64_lower g1))
          (bounded_signed64_nonpositive (bounded_interval64_upper g1)))
        (registered_case10173_fs_hist_u_point_elements
          (bounded_signed64_object_cv (bounded_interval64_lower x2))
          (bounded_signed64_object_cv (bounded_interval64_upper x2))
          (bounded_signed64_nonnegative (bounded_interval64_lower g2))
          (bounded_signed64_nonpositive (bounded_interval64_upper g2))) =
      SOME (bounded_interval64_object_cv upper_value)` by
       (irule registered_case10173_historical_u_value_formula_block_typed_exact
        >> simp []
        >> metis_tac [])
  >> qpat_x_assum
       `registered_case10173_fs_hist_u_point_elements _ _ _ _ = _`
       kall_tac
  >> qpat_x_assum
       `registered_case10173_fs_hist_u_point_elements _ _ _ _ = _`
       kall_tac
  >> qpat_x_assum
       `registered_case10173_fs_hist_u_point_elements _ _ _ _ = _`
       kall_tac
  >> Cases_on `x0`
  >> Cases_on `x1`
  >> Cases_on `x2`
  >> Cases_on `g0`
  >> Cases_on `g1`
  >> Cases_on `g2`
  >> Cases_on `lower_value`
  >> Cases_on `upper_value`
  >> fs
       [compute_registeredCase10173HistoricalUThreeEvalTheory.registered_case10173_fs_hist_u_after_gradients_object_def,
        bounded_object_fs_raw_le_zero_signed_object_cv,
        bounded_object_fs_raw_le_signed_object_cv_zero,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem registered_case10173_historical_u_three_object_typed_exact:
  bounded_historical_u_three_decimal x0 x1 x2 = SOME (value,gradient) ==>
  registered_case10173_fs_hist_u_three_object
      (bounded_interval64_object_cv x0)
      (bounded_interval64_object_cv x1)
      (bounded_interval64_object_cv x2) =
    SOME
      (Pair (bounded_interval64_object_cv value)
        (bounded_interval64_object_cv_list gradient))
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u_three_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_interval_scale_two_object_typed_exact
  >> imp_res_tac
       registered_case10173_historical_u_after_gradients_object_typed_exact
  >> fs
       [compute_registeredCase10173HistoricalUThreeEvalTheory.registered_case10173_fs_hist_u_three_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_historical_u126_object_typed_exact:
  bounded_historical_u126_decimal [x0;x1;x2;x3;x4;x5] =
      SOME (value,gradient) ==>
  registered_case10173_fs_hist_u126_object
      (bounded_interval64_object_cv x0)
      (bounded_interval64_object_cv x1)
      (bounded_interval64_object_cv x2)
      (bounded_interval64_object_cv x3)
      (bounded_interval64_object_cv x4)
      (bounded_interval64_object_cv x5) =
    SOME
      (Pair (bounded_interval64_object_cv value)
        (bounded_interval64_object_cv_list gradient))
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u126_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_historical_u_three_object_typed_exact
  >> fs
       [compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u126_object_def,
        compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u126_embed_local_object_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
        compute_boundedIntervalListTheory.bounded_interval64_zero_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

Theorem registered_case10173_historical_u135_object_typed_exact:
  bounded_historical_u135_decimal [x0;x1;x2;x3;x4;x5] =
      SOME (value,gradient) ==>
  registered_case10173_fs_hist_u135_object
      (bounded_interval64_object_cv x0)
      (bounded_interval64_object_cv x1)
      (bounded_interval64_object_cv x2)
      (bounded_interval64_object_cv x3)
      (bounded_interval64_object_cv x4)
      (bounded_interval64_object_cv x5) =
    SOME
      (Pair (bounded_interval64_object_cv value)
        (bounded_interval64_object_cv_list gradient))
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u135_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_historical_u_three_object_typed_exact
  >> fs
       [compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u135_object_def,
        compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u135_embed_local_object_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
        compute_boundedIntervalListTheory.bounded_interval64_zero_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

val _ = export_theory ();
