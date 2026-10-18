(*****************************************************************************
 * Registered-source refinement for the six historical delta-gradient blocks.
 *
 * The source groups a doubled negative product into one ten-way sum, while
 * the compact checker accumulates eleven signed products.  The common
 * boundary below compares their exact integer endpoints before the single
 * outward decimal rounding step.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaGradientBlockEval
Ancestors
  compute_registeredCase10173HistoricalDeltaBlockPrimitiveEval
  compute_registeredCase10173HistoricalDeltaGradientComponentEval
  compute_boundedObjectHistoricalSecondDecimal
Libs
  bossLib preamble intLib

val _ = monadsyntax.temp_enable_monad "option";

Theorem registered_case10173_interval_scale_neg_two_object_ints_general:
  !source lower upper.
    bounded_object_interval_ints source = SOME (lower,upper) ==>
    ?result.
      registered_case10173_fs_interval_scale_neg_two_object source =
        SOME result /\
      bounded_object_interval_ints result =
        SOME (-2 * upper,-2 * lower)
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
  >> mp_tac
       (Q.SPECL
         [`Pair scaled_lower scaled_upper`,`2 * lower`,`2 * upper`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_interval_neg_signed_values_exists)
  >> impl_tac
  >- simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def]
  >> disch_then (qx_choose_then `result` strip_assume_tac)
  >> qexists_tac `result`
  >> simp
       [compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_scale_neg_two_object_def,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_source_raw_sum_round_fused_exact:
  compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
      source_objects =
    SOME
      (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
        products) /\
  bounded_interval64_fused_products_decimal products = SOME result ==>
  ?raw.
    registered_case10173_fs_interval_sum_object source_objects = SOME raw /\
    bounded_object_fs_raw_interval_round 1000000000000 raw =
      SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
               products)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
               products)`]
         (Q.INST [`values` |-> `source_objects`]
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_signed_values))
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `source_raw` strip_assume_tac)
  >> mp_tac
       (Q.INST [`products` |-> `products`, `result` |-> `result`]
          compute_boundedObjectDecimalFusedTheory.bounded_object_fs_fused_products_decimal_object_exact)
  >> impl_tac >- simp []
  >> disch_then
       (qx_choose_then `compact_lower`
         (qx_choose_then `compact_upper` strip_assume_tac))
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_products_endpoint_values
  >> mp_tac
       (Q.SPECL
         [`source_raw`,`Pair compact_lower compact_upper`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
               products)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
               products)`,
          `1000000000000`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_fs_raw_interval_round_ints_extensional)
  >> impl_tac >- simp []
  >> strip_tac
  >> qexists_tac `source_raw`
  >> simp []
QED

Theorem registered_case10173_raw_product_ints_negated_left:
  !left right.
    compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
      (bounded_interval64_neg left) right =
    (-SND
       (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
         left right),
     -FST
       (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
         left right))
Proof
  rpt gen_tac
  >> Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_ints_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_value,
        compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.bounded_object_int_negated_left_product_extrema]
QED

Theorem registered_case10173_scaled_neg_two_raw_product_exists:
  !left right.
    ?product scaled.
      bounded_object_fs_raw_interval_mul
          (bounded_interval64_object_cv left)
          (bounded_interval64_object_cv right) = SOME product /\
      registered_case10173_fs_interval_scale_neg_two_object product =
        SOME scaled /\
      bounded_object_interval_ints scaled =
        SOME
          (-2 * SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left right),
           -2 * FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left right))
Proof
  rpt gen_tac
  >> mp_tac
       (Q.SPECL [`left`,`right`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `product` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`product`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left right)`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               left right)`]
         registered_case10173_interval_scale_neg_two_object_ints_general)
  >> impl_tac
  >- (mp_tac
       (Q.SPECL [`left`,`right`,`product`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values)
      >> simp [])
  >> disch_then (qx_choose_then `scaled` strip_assume_tac)
  >> qexistsl_tac [`product`,`scaled`]
  >> simp []
QED

fun registered_case10173_raw_product_tac left right product =
  mp_tac
    (Q.SPECL [left,right]
      compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then product strip_assume_tac);

fun registered_case10173_negated_raw_product_tac left right product negative =
  mp_tac
    (Q.SPECL [left,right]
      compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then product (qx_choose_then negative strip_assume_tac));

fun registered_case10173_scaled_neg_two_raw_product_tac
    left right product scaled =
  mp_tac
    (Q.SPECL [left,right]
      registered_case10173_scaled_neg_two_raw_product_exists)
  >> disch_then
       (qx_choose_then product (qx_choose_then scaled strip_assume_tac));

Definition registered_case10173_fs_hist_delta_gradient_block0_object_def:
  registered_case10173_fs_hist_delta_gradient_block0_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      do
        p03 <- bounded_object_fs_raw_interval_mul x0 x3;
        s03 <- registered_case10173_fs_interval_scale_neg_two_object p03;
        p13 <- bounded_object_fs_raw_interval_mul x1 x3;
        p14 <- bounded_object_fs_raw_interval_mul x1 x4;
        p15 <- bounded_object_fs_raw_interval_mul x1 x5;
        n15 <- bounded_object_fs_interval_neg p15;
        p23 <- bounded_object_fs_raw_interval_mul x2 x3;
        p24 <- bounded_object_fs_raw_interval_mul x2 x4;
        n24 <- bounded_object_fs_interval_neg p24;
        p25 <- bounded_object_fs_raw_interval_mul x2 x5;
        p33 <- bounded_object_fs_raw_interval_mul x3 x3;
        n33 <- bounded_object_fs_interval_neg p33;
        p34 <- bounded_object_fs_raw_interval_mul x3 x4;
        p35 <- bounded_object_fs_raw_interval_mul x3 x5;
        raw <- registered_case10173_fs_interval_sum_object
          [s03;p13;p14;n15;p23;n24;p25;n33;p34;p35];
        bounded_object_fs_raw_interval_round 1000000000000 raw
      od
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_gradient_block0_object_typed_exact:
  bounded_historical_delta_gradient_component_decimal 0 environment =
      SOME result ==>
  registered_case10173_fs_hist_delta_gradient_block0_object
      (MAP bounded_interval64_object_cv environment) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> mp_tac
       (Q.SPECL [`h`,`h'³'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p03` strip_assume_tac)
  >> mp_tac
       (Q.SPECL
         [`p03`,
          `FST
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               h h'³')`,
          `SND
             (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
               h h'³')`]
         registered_case10173_interval_scale_neg_two_object_ints_general)
  >> impl_tac
  >- (mp_tac
       (Q.SPECL [`h`,`h'³'`,`p03`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values)
      >> simp [])
  >> disch_then (qx_choose_then `s03` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`h'`,`h'³'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p13` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`h'`,`h'⁴'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p14` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`h'`,`h'⁵'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then `p15` (qx_choose_then `n15` strip_assume_tac))
  >> mp_tac
       (Q.SPECL [`h''`,`h'³'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p23` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`h''`,`h'⁴'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then `p24` (qx_choose_then `n24` strip_assume_tac))
  >> mp_tac
       (Q.SPECL [`h''`,`h'⁵'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p25` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`h'³'`,`h'³'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_exists)
  >> disch_then
       (qx_choose_then `p33` (qx_choose_then `n33` strip_assume_tac))
  >> mp_tac
       (Q.SPECL [`h'³'`,`h'⁴'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p34` strip_assume_tac)
  >> mp_tac
       (Q.SPECL [`h'³'`,`h'⁵'`]
          compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `p35` strip_assume_tac)
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [s03;p13;p14;n15;p23;n24;p25;n33;p34;p35] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(bounded_interval64_neg h,h'³');
           (bounded_interval64_neg h,h'³');
           (h',h'³');(h',h'⁴');(bounded_interval64_neg h',h'⁵');
           (h'',h'³');(bounded_interval64_neg h'',h'⁴');(h'',h'⁵');
           (bounded_interval64_neg h'³',h'³');(h'³',h'⁴');
           (h'³',h'⁵')])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           registered_case10173_raw_product_ints_negated_left,LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'³' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'³' h'⁵'`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac registered_case10173_source_raw_sum_round_fused_exact
  >> fs [registered_case10173_fs_hist_delta_gradient_block0_object_def]
QED

Definition registered_case10173_fs_hist_delta_gradient_block1_object_def:
  registered_case10173_fs_hist_delta_gradient_block1_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      do
        p03 <- bounded_object_fs_raw_interval_mul x0 x3;
        p04 <- bounded_object_fs_raw_interval_mul x0 x4;
        p05 <- bounded_object_fs_raw_interval_mul x0 x5;
        n05 <- bounded_object_fs_interval_neg p05;
        p14 <- bounded_object_fs_raw_interval_mul x1 x4;
        s14 <- registered_case10173_fs_interval_scale_neg_two_object p14;
        p23 <- bounded_object_fs_raw_interval_mul x2 x3;
        n23 <- bounded_object_fs_interval_neg p23;
        p24 <- bounded_object_fs_raw_interval_mul x2 x4;
        p25 <- bounded_object_fs_raw_interval_mul x2 x5;
        p34 <- bounded_object_fs_raw_interval_mul x3 x4;
        p44 <- bounded_object_fs_raw_interval_mul x4 x4;
        n44 <- bounded_object_fs_interval_neg p44;
        p45 <- bounded_object_fs_raw_interval_mul x4 x5;
        raw <- registered_case10173_fs_interval_sum_object
          [p03;p04;n05;s14;n23;p24;p25;p34;n44;p45];
        bounded_object_fs_raw_interval_round 1000000000000 raw
      od
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_gradient_block1_object_typed_exact:
  bounded_historical_delta_gradient_component_decimal 1 environment =
      SOME result ==>
  registered_case10173_fs_hist_delta_gradient_block1_object
      (MAP bounded_interval64_object_cv environment) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> registered_case10173_raw_product_tac `h` `h'³'` `p03`
  >> registered_case10173_raw_product_tac `h` `h'⁴'` `p04`
  >> registered_case10173_negated_raw_product_tac `h` `h'⁵'` `p05` `n05`
  >> registered_case10173_scaled_neg_two_raw_product_tac
       `h'` `h'⁴'` `p14` `s14`
  >> registered_case10173_negated_raw_product_tac
       `h''` `h'³'` `p23` `n23`
  >> registered_case10173_raw_product_tac `h''` `h'⁴'` `p24`
  >> registered_case10173_raw_product_tac `h''` `h'⁵'` `p25`
  >> registered_case10173_raw_product_tac `h'³'` `h'⁴'` `p34`
  >> registered_case10173_negated_raw_product_tac
       `h'⁴'` `h'⁴'` `p44` `n44`
  >> registered_case10173_raw_product_tac `h'⁴'` `h'⁵'` `p45`
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [p03;p04;n05;s14;n23;p24;p25;p34;n44;p45] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(h,h'³');(h,h'⁴');(bounded_interval64_neg h,h'⁵');
           (bounded_interval64_neg h',h'⁴');
           (bounded_interval64_neg h',h'⁴');
           (bounded_interval64_neg h'',h'³');(h'',h'⁴');(h'',h'⁵');
           (h'³',h'⁴');(bounded_interval64_neg h'⁴',h'⁴');
           (h'⁴',h'⁵')])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           registered_case10173_raw_product_ints_negated_left,LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'³' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'⁴' h'⁵'`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac registered_case10173_source_raw_sum_round_fused_exact
  >> fs [registered_case10173_fs_hist_delta_gradient_block1_object_def]
QED

Definition registered_case10173_fs_hist_delta_gradient_block2_object_def:
  registered_case10173_fs_hist_delta_gradient_block2_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      do
        p03 <- bounded_object_fs_raw_interval_mul x0 x3;
        p04 <- bounded_object_fs_raw_interval_mul x0 x4;
        n04 <- bounded_object_fs_interval_neg p04;
        p05 <- bounded_object_fs_raw_interval_mul x0 x5;
        p13 <- bounded_object_fs_raw_interval_mul x1 x3;
        n13 <- bounded_object_fs_interval_neg p13;
        p14 <- bounded_object_fs_raw_interval_mul x1 x4;
        p15 <- bounded_object_fs_raw_interval_mul x1 x5;
        p25 <- bounded_object_fs_raw_interval_mul x2 x5;
        s25 <- registered_case10173_fs_interval_scale_neg_two_object p25;
        p35 <- bounded_object_fs_raw_interval_mul x3 x5;
        p45 <- bounded_object_fs_raw_interval_mul x4 x5;
        p55 <- bounded_object_fs_raw_interval_mul x5 x5;
        n55 <- bounded_object_fs_interval_neg p55;
        raw <- registered_case10173_fs_interval_sum_object
          [p03;n04;p05;n13;p14;p15;s25;p35;p45;n55];
        bounded_object_fs_raw_interval_round 1000000000000 raw
      od
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_gradient_block2_object_typed_exact:
  bounded_historical_delta_gradient_component_decimal 2 environment =
      SOME result ==>
  registered_case10173_fs_hist_delta_gradient_block2_object
      (MAP bounded_interval64_object_cv environment) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> registered_case10173_raw_product_tac `h` `h'³'` `p03`
  >> registered_case10173_negated_raw_product_tac `h` `h'⁴'` `p04` `n04`
  >> registered_case10173_raw_product_tac `h` `h'⁵'` `p05`
  >> registered_case10173_negated_raw_product_tac
       `h'` `h'³'` `p13` `n13`
  >> registered_case10173_raw_product_tac `h'` `h'⁴'` `p14`
  >> registered_case10173_raw_product_tac `h'` `h'⁵'` `p15`
  >> registered_case10173_scaled_neg_two_raw_product_tac
       `h''` `h'⁵'` `p25` `s25`
  >> registered_case10173_raw_product_tac `h'³'` `h'⁵'` `p35`
  >> registered_case10173_raw_product_tac `h'⁴'` `h'⁵'` `p45`
  >> registered_case10173_negated_raw_product_tac
       `h'⁵'` `h'⁵'` `p55` `n55`
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [p03;n04;p05;n13;p14;p15;s25;p35;p45;n55] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(h,h'³');(bounded_interval64_neg h,h'⁴');(h,h'⁵');
           (bounded_interval64_neg h',h'³');(h',h'⁴');(h',h'⁵');
           (bounded_interval64_neg h'',h'⁵');
           (bounded_interval64_neg h'',h'⁵');
           (h'³',h'⁵');(h'⁴',h'⁵');
           (bounded_interval64_neg h'⁵',h'⁵')])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           registered_case10173_raw_product_ints_negated_left,LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'³' h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'⁴' h'⁵'`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac registered_case10173_source_raw_sum_round_fused_exact
  >> fs [registered_case10173_fs_hist_delta_gradient_block2_object_def]
QED

Definition registered_case10173_fs_hist_delta_gradient_block3_object_def:
  registered_case10173_fs_hist_delta_gradient_block3_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      do
        p00 <- bounded_object_fs_raw_interval_mul x0 x0;
        n00 <- bounded_object_fs_interval_neg p00;
        p01 <- bounded_object_fs_raw_interval_mul x0 x1;
        p02 <- bounded_object_fs_raw_interval_mul x0 x2;
        p03 <- bounded_object_fs_raw_interval_mul x0 x3;
        s03 <- registered_case10173_fs_interval_scale_neg_two_object p03;
        p04 <- bounded_object_fs_raw_interval_mul x0 x4;
        p05 <- bounded_object_fs_raw_interval_mul x0 x5;
        p12 <- bounded_object_fs_raw_interval_mul x1 x2;
        n12 <- bounded_object_fs_interval_neg p12;
        p14 <- bounded_object_fs_raw_interval_mul x1 x4;
        p25 <- bounded_object_fs_raw_interval_mul x2 x5;
        p45 <- bounded_object_fs_raw_interval_mul x4 x5;
        n45 <- bounded_object_fs_interval_neg p45;
        raw <- registered_case10173_fs_interval_sum_object
          [n00;p01;p02;s03;p04;p05;n12;p14;p25;n45];
        bounded_object_fs_raw_interval_round 1000000000000 raw
      od
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_gradient_block3_object_typed_exact:
  bounded_historical_delta_gradient_component_decimal 3 environment =
      SOME result ==>
  registered_case10173_fs_hist_delta_gradient_block3_object
      (MAP bounded_interval64_object_cv environment) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> registered_case10173_negated_raw_product_tac `h` `h` `p00` `n00`
  >> registered_case10173_raw_product_tac `h` `h'` `p01`
  >> registered_case10173_raw_product_tac `h` `h''` `p02`
  >> registered_case10173_scaled_neg_two_raw_product_tac
       `h` `h'³'` `p03` `s03`
  >> registered_case10173_raw_product_tac `h` `h'⁴'` `p04`
  >> registered_case10173_raw_product_tac `h` `h'⁵'` `p05`
  >> registered_case10173_negated_raw_product_tac `h'` `h''` `p12` `n12`
  >> registered_case10173_raw_product_tac `h'` `h'⁴'` `p14`
  >> registered_case10173_raw_product_tac `h''` `h'⁵'` `p25`
  >> registered_case10173_negated_raw_product_tac
       `h'⁴'` `h'⁵'` `p45` `n45`
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [n00;p01;p02;s03;p04;p05;n12;p14;p25;n45] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(bounded_interval64_neg h,h);(h,h');(h,h'');
           (bounded_interval64_neg h,h'³');
           (bounded_interval64_neg h,h'³');
           (h,h'⁴');(h,h'⁵');(bounded_interval64_neg h',h'');
           (h',h'⁴');(h'',h'⁵');
           (bounded_interval64_neg h'⁴',h'⁵')])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           registered_case10173_raw_product_ints_negated_left,LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h''`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'⁵'`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac registered_case10173_source_raw_sum_round_fused_exact
  >> fs [registered_case10173_fs_hist_delta_gradient_block3_object_def]
QED

Definition registered_case10173_fs_hist_delta_gradient_block4_object_def:
  registered_case10173_fs_hist_delta_gradient_block4_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      do
        p01 <- bounded_object_fs_raw_interval_mul x0 x1;
        p02 <- bounded_object_fs_raw_interval_mul x0 x2;
        n02 <- bounded_object_fs_interval_neg p02;
        p03 <- bounded_object_fs_raw_interval_mul x0 x3;
        p11 <- bounded_object_fs_raw_interval_mul x1 x1;
        n11 <- bounded_object_fs_interval_neg p11;
        p12 <- bounded_object_fs_raw_interval_mul x1 x2;
        p13 <- bounded_object_fs_raw_interval_mul x1 x3;
        p14 <- bounded_object_fs_raw_interval_mul x1 x4;
        s14 <- registered_case10173_fs_interval_scale_neg_two_object p14;
        p15 <- bounded_object_fs_raw_interval_mul x1 x5;
        p25 <- bounded_object_fs_raw_interval_mul x2 x5;
        p35 <- bounded_object_fs_raw_interval_mul x3 x5;
        n35 <- bounded_object_fs_interval_neg p35;
        raw <- registered_case10173_fs_interval_sum_object
          [p01;n02;p03;n11;p12;p13;s14;p15;p25;n35];
        bounded_object_fs_raw_interval_round 1000000000000 raw
      od
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_gradient_block4_object_typed_exact:
  bounded_historical_delta_gradient_component_decimal 4 environment =
      SOME result ==>
  registered_case10173_fs_hist_delta_gradient_block4_object
      (MAP bounded_interval64_object_cv environment) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> registered_case10173_raw_product_tac `h` `h'` `p01`
  >> registered_case10173_negated_raw_product_tac `h` `h''` `p02` `n02`
  >> registered_case10173_raw_product_tac `h` `h'³'` `p03`
  >> registered_case10173_negated_raw_product_tac `h'` `h'` `p11` `n11`
  >> registered_case10173_raw_product_tac `h'` `h''` `p12`
  >> registered_case10173_raw_product_tac `h'` `h'³'` `p13`
  >> registered_case10173_scaled_neg_two_raw_product_tac
       `h'` `h'⁴'` `p14` `s14`
  >> registered_case10173_raw_product_tac `h'` `h'⁵'` `p15`
  >> registered_case10173_raw_product_tac `h''` `h'⁵'` `p25`
  >> registered_case10173_negated_raw_product_tac
       `h'³'` `h'⁵'` `p35` `n35`
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [p01;n02;p03;n11;p12;p13;s14;p15;p25;n35] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(h,h');(bounded_interval64_neg h,h'');(h,h'³');
           (bounded_interval64_neg h',h');(h',h'');(h',h'³');
           (bounded_interval64_neg h',h'⁴');
           (bounded_interval64_neg h',h'⁴');
           (h',h'⁵');(h'',h'⁵');
           (bounded_interval64_neg h'³',h'⁵')])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           registered_case10173_raw_product_ints_negated_left,LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h''`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'⁵'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'⁵'`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac registered_case10173_source_raw_sum_round_fused_exact
  >> fs [registered_case10173_fs_hist_delta_gradient_block4_object_def]
QED

Definition registered_case10173_fs_hist_delta_gradient_block5_object_def:
  registered_case10173_fs_hist_delta_gradient_block5_object environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      do
        p01 <- bounded_object_fs_raw_interval_mul x0 x1;
        n01 <- bounded_object_fs_interval_neg p01;
        p02 <- bounded_object_fs_raw_interval_mul x0 x2;
        p03 <- bounded_object_fs_raw_interval_mul x0 x3;
        p12 <- bounded_object_fs_raw_interval_mul x1 x2;
        p14 <- bounded_object_fs_raw_interval_mul x1 x4;
        p22 <- bounded_object_fs_raw_interval_mul x2 x2;
        n22 <- bounded_object_fs_interval_neg p22;
        p23 <- bounded_object_fs_raw_interval_mul x2 x3;
        p24 <- bounded_object_fs_raw_interval_mul x2 x4;
        p25 <- bounded_object_fs_raw_interval_mul x2 x5;
        s25 <- registered_case10173_fs_interval_scale_neg_two_object p25;
        p34 <- bounded_object_fs_raw_interval_mul x3 x4;
        n34 <- bounded_object_fs_interval_neg p34;
        raw <- registered_case10173_fs_interval_sum_object
          [n01;p02;p03;p12;p14;n22;p23;p24;s25;n34];
        bounded_object_fs_raw_interval_round 1000000000000 raw
      od
    | _ => NONE
End

Theorem registered_case10173_fs_hist_delta_gradient_block5_object_typed_exact:
  bounded_historical_delta_gradient_component_decimal 5 environment =
      SOME result ==>
  registered_case10173_fs_hist_delta_gradient_block5_object
      (MAP bounded_interval64_object_cv environment) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> registered_case10173_negated_raw_product_tac `h` `h'` `p01` `n01`
  >> registered_case10173_raw_product_tac `h` `h''` `p02`
  >> registered_case10173_raw_product_tac `h` `h'³'` `p03`
  >> registered_case10173_raw_product_tac `h'` `h''` `p12`
  >> registered_case10173_raw_product_tac `h'` `h'⁴'` `p14`
  >> registered_case10173_negated_raw_product_tac `h''` `h''` `p22` `n22`
  >> registered_case10173_raw_product_tac `h''` `h'³'` `p23`
  >> registered_case10173_raw_product_tac `h''` `h'⁴'` `p24`
  >> registered_case10173_scaled_neg_two_raw_product_tac
       `h''` `h'⁵'` `p25` `s25`
  >> registered_case10173_negated_raw_product_tac
       `h'³'` `h'⁴'` `p34` `n34`
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_endpoint_values
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_negated_raw_product_endpoint_values
  >> `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_interval_ints_sum
        [n01;p02;p03;p12;p14;n22;p23;p24;s25;n34] =
      SOME
        (compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_products_ints_sum
          [(bounded_interval64_neg h,h');(h,h'');(h,h'³');
           (h',h'');(h',h'⁴');(bounded_interval64_neg h'',h'');
           (h'',h'³');(h'',h'⁴');
           (bounded_interval64_neg h'',h'⁵');
           (bounded_interval64_neg h'',h'⁵');
           (bounded_interval64_neg h'³',h'⁴')])` by
       (fs
          [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_ints_sum_def,
           compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_products_ints_sum_def,
           registered_case10173_raw_product_ints_negated_left,LET_THM]
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h''`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h''`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h' h'⁴'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'³'`
        >> Cases_on
             `compute_registeredCase10173HistoricalDeltaX4ValueBlockEval$registered_case10173_raw_product_ints
                h'' h'⁴'`
        >> simp []
        >> intLib.ARITH_TAC)
  >> imp_res_tac registered_case10173_source_raw_sum_round_fused_exact
  >> fs [registered_case10173_fs_hist_delta_gradient_block5_object_def]
QED

val _ = export_theory ();
