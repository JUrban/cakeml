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

val _ = export_theory ();
