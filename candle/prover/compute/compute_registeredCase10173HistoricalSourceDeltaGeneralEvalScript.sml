(*****************************************************************************
 * Packet-independent evaluator refinement for the registered source-shaped
 * delta value.
 *
 * The production checker uses a tighter fused cubic calculation for the
 * numerical bound.  The registered source evaluates the same polynomial
 * with ordinary decimal interval operations and a right-associated sum.  Its
 * local result is dead, but successful source evaluation is still part of the
 * semantic contract.  The packet checker therefore performs this small
 * source-shaped calculation as an explicit compatibility check; the theorems
 * below connect that check to the registered evaluator without equating the
 * two differently rounded interval results.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSourceDeltaGeneralEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4GeneralEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_source_interval_sum_decimal_object_exact:
  !values result.
    bounded_source_interval64_sum_decimal values = SOME result ==>
    registered_case10173_fs_interval_sum_object
        (MAP bounded_interval64_object_cv values) =
      SOME (bounded_interval64_object_cv result)
Proof
  Induct
  THENL
    [simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_interval64_sum_decimal_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        compute_boundedIntervalListTheory.bounded_interval64_zero_def],
     rw
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_interval64_sum_decimal_def]
     >> (Cases_on `bounded_source_interval64_sum_decimal values`
         THENL
           [gvs [],
            gvs []
            >> imp_res_tac
                 compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
            >> simp
                 [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def]])]
QED

Theorem registered_case10173_source_delta64_value_six_decimal_object_exact:
  bounded_source_delta64_value_six_decimal x0 x1 x2 x3 x4 x5 =
      SOME result ==>
  registered_case10173_fs_angle_delta_value_object
      (bounded_interval64_object_cv x0)
      (bounded_interval64_object_cv x1)
      (bounded_interval64_object_cv x2)
      (bounded_interval64_object_cv x3)
      (bounded_interval64_object_cv x4)
      (bounded_interval64_object_cv x5) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_six_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaValueEvalTheory.registered_case10173_fs_angle_delta_value_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_component0_object_exact:
  bounded_source_delta64_gradient_component_decimal 0
      [p00;p01;p02;p03;p04;p05;p11;p12;p13;p14;p15;
       p22;p23;p24;p25;p33;p34;p35;p44;p45;p55] = SOME result ==>
  registered_case10173_fs_angle_delta_gradient_component0_object
      (bounded_interval64_object_cv p03)
      (bounded_interval64_object_cv p13)
      (bounded_interval64_object_cv p14)
      (bounded_interval64_object_cv p15)
      (bounded_interval64_object_cv p23)
      (bounded_interval64_object_cv p24)
      (bounded_interval64_object_cv p25)
      (bounded_interval64_object_cv p33)
      (bounded_interval64_object_cv p34)
      (bounded_interval64_object_cv p35) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component0_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_component1_object_exact:
  bounded_source_delta64_gradient_component_decimal 1
      [p00;p01;p02;p03;p04;p05;p11;p12;p13;p14;p15;
       p22;p23;p24;p25;p33;p34;p35;p44;p45;p55] = SOME result ==>
  registered_case10173_fs_angle_delta_gradient_component1_object
      (bounded_interval64_object_cv p03)
      (bounded_interval64_object_cv p04)
      (bounded_interval64_object_cv p05)
      (bounded_interval64_object_cv p14)
      (bounded_interval64_object_cv p23)
      (bounded_interval64_object_cv p24)
      (bounded_interval64_object_cv p25)
      (bounded_interval64_object_cv p34)
      (bounded_interval64_object_cv p44)
      (bounded_interval64_object_cv p45) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component1_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_component2_object_exact:
  bounded_source_delta64_gradient_component_decimal 2
      [p00;p01;p02;p03;p04;p05;p11;p12;p13;p14;p15;
       p22;p23;p24;p25;p33;p34;p35;p44;p45;p55] = SOME result ==>
  registered_case10173_fs_angle_delta_gradient_component2_object
      (bounded_interval64_object_cv p03)
      (bounded_interval64_object_cv p04)
      (bounded_interval64_object_cv p05)
      (bounded_interval64_object_cv p13)
      (bounded_interval64_object_cv p14)
      (bounded_interval64_object_cv p15)
      (bounded_interval64_object_cv p25)
      (bounded_interval64_object_cv p35)
      (bounded_interval64_object_cv p45)
      (bounded_interval64_object_cv p55) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component2_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_component3_object_exact:
  bounded_source_delta64_gradient_component_decimal 3
      [p00;p01;p02;p03;p04;p05;p11;p12;p13;p14;p15;
       p22;p23;p24;p25;p33;p34;p35;p44;p45;p55] = SOME result ==>
  registered_case10173_fs_angle_delta_gradient_component3_object
      (bounded_interval64_object_cv p00)
      (bounded_interval64_object_cv p01)
      (bounded_interval64_object_cv p02)
      (bounded_interval64_object_cv p03)
      (bounded_interval64_object_cv p04)
      (bounded_interval64_object_cv p05)
      (bounded_interval64_object_cv p12)
      (bounded_interval64_object_cv p14)
      (bounded_interval64_object_cv p25)
      (bounded_interval64_object_cv p45) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component3_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_component4_object_exact:
  bounded_source_delta64_gradient_component_decimal 4
      [p00;p01;p02;p03;p04;p05;p11;p12;p13;p14;p15;
       p22;p23;p24;p25;p33;p34;p35;p44;p45;p55] = SOME result ==>
  registered_case10173_fs_angle_delta_gradient_component4_object
      (bounded_interval64_object_cv p01)
      (bounded_interval64_object_cv p02)
      (bounded_interval64_object_cv p03)
      (bounded_interval64_object_cv p11)
      (bounded_interval64_object_cv p12)
      (bounded_interval64_object_cv p13)
      (bounded_interval64_object_cv p14)
      (bounded_interval64_object_cv p15)
      (bounded_interval64_object_cv p25)
      (bounded_interval64_object_cv p35) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component4_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_component5_object_exact:
  bounded_source_delta64_gradient_component_decimal 5
      [p00;p01;p02;p03;p04;p05;p11;p12;p13;p14;p15;
       p22;p23;p24;p25;p33;p34;p35;p44;p45;p55] = SOME result ==>
  registered_case10173_fs_angle_delta_gradient_component5_object
      (bounded_interval64_object_cv p01)
      (bounded_interval64_object_cv p02)
      (bounded_interval64_object_cv p03)
      (bounded_interval64_object_cv p12)
      (bounded_interval64_object_cv p14)
      (bounded_interval64_object_cv p22)
      (bounded_interval64_object_cv p23)
      (bounded_interval64_object_cv p24)
      (bounded_interval64_object_cv p25)
      (bounded_interval64_object_cv p34) =
    SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_source_interval_sum_decimal_object_exact
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_scale_neg_two_object_typed_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientComponentEvalTheory.registered_case10173_fs_angle_delta_gradient_component5_object_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_source_delta_gradient_components_length:
  !coordinates products result.
    bounded_source_delta64_gradient_components_decimal coordinates products =
      SOME result ==>
    LENGTH result = LENGTH coordinates
Proof
  Induct
  >> rw
       [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_components_decimal_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_source_delta_gradient_components_cons_exact:
  bounded_source_delta64_gradient_components_decimal
      (coordinate::coordinates) products = SOME (entry::rest) ==>
  bounded_source_delta64_gradient_component_decimal coordinate products =
      SOME entry /\
  bounded_source_delta64_gradient_components_decimal coordinates products =
      SOME rest
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_components_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_object_pairwise_mul_cons_exact:
  bounded_object_fs_interval_list_pairwise_mul_decimal
      (Pair left left_rest) (Pair right right_rest) =
      SOME (Pair value rest) ==>
  bounded_object_fs_interval_mul_decimal left right = SOME value /\
  bounded_object_fs_interval_list_pairwise_mul_decimal
      left_rest right_rest = SOME rest
Proof
  rw
    [compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_list_pairwise_mul_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_source_delta64_gradient_six_decimal_object_exact:
  bounded_source_delta64_gradient_decimal [x0;x1;x2;x3;x4;x5] =
      SOME result ==>
  registered_case10173_fs_angle_delta_gradient_object
      (bounded_interval64_object_cv x0)
      (bounded_interval64_object_cv x1)
      (bounded_interval64_object_cv x2)
      (bounded_interval64_object_cv x3)
      (bounded_interval64_object_cv x4)
      (bounded_interval64_object_cv x5) =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_delta64_pair_products_decimal_exact
  >> qpat_x_assum
       `bounded_delta64_pair_products_decimal _ = SOME _`
       mp_tac
  >> simp
       [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_delta64_pair_products_decimal_def]
  >> strip_tac
  >> imp_res_tac
       compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_interval64_list_pairwise_mul_decimal_length
  >> imp_res_tac registered_case10173_source_delta_gradient_components_length
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> qpat_x_assum
       `bounded_object_fs_delta64_pair_products_decimal _ = SOME _`
       mp_tac
  >> simp
       [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_delta64_pair_products_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> strip_tac
  >> NTAC 21
       (imp_res_tac registered_case10173_object_pairwise_mul_cons_exact)
  >> NTAC 6
       (imp_res_tac
          registered_case10173_source_delta_gradient_components_cons_exact)
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac registered_case10173_source_delta_gradient_component0_object_exact
  >> imp_res_tac registered_case10173_source_delta_gradient_component1_object_exact
  >> imp_res_tac registered_case10173_source_delta_gradient_component2_object_exact
  >> imp_res_tac registered_case10173_source_delta_gradient_component3_object_exact
  >> imp_res_tac registered_case10173_source_delta_gradient_component4_object_exact
  >> imp_res_tac registered_case10173_source_delta_gradient_component5_object_exact
  >> gvs
       [compute_registeredCase10173HistoricalDeltaGradientEvalTheory.registered_case10173_fs_angle_delta_gradient_object_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_delta_pair_products_decimal_lengths:
  bounded_delta64_pair_products_decimal environment = SOME products ==>
  LENGTH environment = 6 /\ LENGTH products = 21
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_delta64_pair_products_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_interval64_list_pairwise_mul_decimal_length
  >> gvs []
QED

Theorem registered_case10173_source_delta64_gradient_decimal_lengths:
  bounded_source_delta64_gradient_decimal environment = SOME result ==>
  LENGTH environment = 6 /\ LENGTH result = 6
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_delta_pair_products_decimal_lengths
  >> imp_res_tac registered_case10173_source_delta_gradient_components_length
  >> gvs []
QED

Theorem registered_case10173_source_delta64_gradient_decimal_eval:
  bounded_source_delta64_gradient_decimal environment = SOME result /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient»
        [from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> imp_res_tac registered_case10173_source_delta64_gradient_decimal_lengths
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> drule registered_case10173_source_delta64_gradient_six_decimal_object_exact
  >> strip_tac
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalDeltaX4GeneralEvalTheory.registered_case10173_bounded_interval64_object_cv_list_six]
  >> irule
       compute_registeredCase10173HistoricalDeltaGradientEvalTheory.registered_case10173_fs_angle_delta_gradient_object_eval
  >> simp
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_source_delta64_value_decimal_eval:
  bounded_source_delta64_value_decimal environment = SOME result /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value»
        [from_cv (bounded_interval64_object_cv_list environment)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  Cases_on `environment`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> Cases_on `t`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> Cases_on `t'`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> Cases_on `t`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> Cases_on `t'`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> Cases_on `t`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> Cases_on `t'`
  >> simp
       [compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def]
  >> rpt strip_tac
  >> drule registered_case10173_source_delta64_value_six_decimal_object_exact
  >> strip_tac
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalDeltaX4GeneralEvalTheory.registered_case10173_bounded_interval64_object_cv_list_six]
  >> irule
       compute_registeredCase10173HistoricalDeltaValueEvalTheory.registered_case10173_fs_angle_delta_value_object_eval
  >> simp []
QED

val _ = export_theory ();
