(*****************************************************************************
 * Closed registered first-order evaluation for the authenticated genuine
 * case-10173 center packet.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalFirstOrderCenterEval
Ancestors
  compute_registeredCase10173HistoricalFirstOrderEval
  compute_registeredCase10173HistoricalDeltaCenterEval
  compute_boundedCase10173HistoricalCellDecimalBoundary
Libs
  bossLib preamble wordsLib

Definition registered_case10173_historical_center_environment_decimal_def:
  registered_case10173_historical_center_environment_decimal =
    bounded_case10173_packet_center_environment
      bounded_case10173_decimal_packet0_source_aligned
End

Definition registered_case10173_historical_center_root_delta_def:
  registered_case10173_historical_center_root_delta =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => center_root_delta
End

Definition registered_case10173_historical_center_root_four_x0_def:
  registered_case10173_historical_center_root_four_x0 =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => center_root_four_x0
End

Definition registered_case10173_historical_center_reciprocals_def:
  registered_case10173_historical_center_reciprocals =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => center_reciprocals
End

Definition registered_case10173_historical_center_root_derivative_def:
  registered_case10173_historical_center_root_derivative =
    EL 0 registered_case10173_historical_center_reciprocals
End

Definition registered_case10173_historical_center_root_four_reciprocal_def:
  registered_case10173_historical_center_root_four_reciprocal =
    EL 1 registered_case10173_historical_center_reciprocals
End

Definition registered_case10173_historical_center_u_reciprocal_def:
  registered_case10173_historical_center_u_reciprocal =
    EL 2 registered_case10173_historical_center_reciprocals
End

Definition registered_case10173_historical_center_special_root_reciprocal_def:
  registered_case10173_historical_center_special_root_reciprocal =
    EL 3 registered_case10173_historical_center_reciprocals
End

Definition registered_case10173_historical_center_b_reciprocal_def:
  registered_case10173_historical_center_b_reciprocal =
    EL 4 registered_case10173_historical_center_reciprocals
End

Definition registered_case10173_historical_center_delta_products_def:
  registered_case10173_historical_center_delta_products =
    THE
      (bounded_delta64_pair_products_decimal
        registered_case10173_historical_center_environment_decimal)
End

Definition registered_case10173_historical_center_delta_gradient_def:
  registered_case10173_historical_center_delta_gradient =
    THE
      (bounded_delta64_gradient_from_products
        registered_case10173_historical_center_delta_products)
End

Definition registered_case10173_historical_center_delta_gradient_expected_def:
  registered_case10173_historical_center_delta_gradient_expected =
    [BoundedInterval64
       (BoundedSigned64 F 10307984924270w)
       (BoundedSigned64 F 10307984924371w);
     BoundedInterval64
       (BoundedSigned64 F 19421892394972w)
       (BoundedSigned64 F 19421892395074w);
     BoundedInterval64
       (BoundedSigned64 F 19337032470656w)
       (BoundedSigned64 F 19337032470758w);
     BoundedInterval64
       (BoundedSigned64 F 15967634875440w)
       (BoundedSigned64 F 15967634875546w);
     BoundedInterval64
       (BoundedSigned64 F 19559381848098w)
       (BoundedSigned64 F 19559381848200w);
     BoundedInterval64
       (BoundedSigned64 F 19155801287796w)
       (BoundedSigned64 F 19155801287898w)]
End

Theorem registered_case10173_historical_center_specialized_first_exists:
  ?value gradient.
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals =>
      bounded_historical_dihedral_first64_decimal center_environment
        center_root_delta center_root_four_x0 center_reciprocals =
      SOME (value,gradient)
Proof
  mp_tac
    compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_accepts
  >> strip_tac
  >> drule
       compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_accepts_complete_contract
  >> simp
       [compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_complete_contract_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
        compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> metis_tac [pairTheory.PAIR]
QED

Theorem registered_case10173_historical_center_specialized_first_named:
  ?value gradient.
    bounded_historical_dihedral_first64_decimal
      registered_case10173_historical_center_environment_decimal
      registered_case10173_historical_center_root_delta
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_reciprocals =
    SOME (value,gradient)
Proof
  mp_tac registered_case10173_historical_center_specialized_first_exists
  >> Cases_on `bounded_case10173_decimal_packet0_source_aligned`
  >> simp
       [registered_case10173_historical_center_environment_decimal_def,
        registered_case10173_historical_center_root_delta_def,
        registered_case10173_historical_center_root_four_x0_def,
        registered_case10173_historical_center_reciprocals_def,
        compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def]
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_reciprocals_components:
  registered_case10173_historical_center_reciprocals =
    [registered_case10173_historical_center_root_derivative;
     registered_case10173_historical_center_root_four_reciprocal;
     registered_case10173_historical_center_u_reciprocal;
     registered_case10173_historical_center_special_root_reciprocal;
     registered_case10173_historical_center_b_reciprocal]
Proof
  EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_products_eval:
  bounded_delta64_pair_products_decimal
      registered_case10173_historical_center_environment_decimal =
    SOME registered_case10173_historical_center_delta_products
Proof
  simp
    [registered_case10173_historical_center_delta_products_def,
     registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_gradient_eval:
  bounded_delta64_gradient_from_products
      registered_case10173_historical_center_delta_products =
    SOME registered_case10173_historical_center_delta_gradient
Proof
  simp
    [registered_case10173_historical_center_delta_gradient_def,
     registered_case10173_historical_center_delta_products_def,
     registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_gradient_pipeline:
  (case bounded_delta64_pair_products_decimal
      registered_case10173_historical_center_environment_decimal of
   | NONE => NONE
   | SOME products => bounded_delta64_gradient_from_products products) =
  SOME registered_case10173_historical_center_delta_gradient_expected
Proof
  simp
    [registered_case10173_historical_center_environment_decimal_def,
     registered_case10173_historical_center_delta_gradient_expected_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_gradient_object_expected:
  registered_case10173_fs_angle_delta_gradient_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 =
    SOME
      (bounded_interval64_object_cv_list
        registered_case10173_historical_center_delta_gradient_expected)
Proof
  simp
    [registered_case10173_historical_center_delta_gradient_expected_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x0_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x1_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x2_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x3_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x4_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x5_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_gradient_matches:
  bounded_delta64_pair_products_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME products /\
  bounded_delta64_gradient_from_products products = SOME gradient ==>
  registered_case10173_fs_angle_delta_gradient_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 =
    SOME (bounded_interval64_object_cv_list gradient)
Proof
  rpt strip_tac
  >> `((case bounded_delta64_pair_products_decimal
            registered_case10173_historical_center_environment_decimal of
         | NONE => NONE
         | SOME products => bounded_delta64_gradient_from_products products) =
       SOME gradient)` by simp []
  >> gvs
       [registered_case10173_historical_center_delta_gradient_pipeline,
        registered_case10173_historical_center_delta_gradient_object_expected]
QED

Theorem registered_case10173_historical_center_delta_source_values:
  ?delta_interval delta_products delta_gradient.
    bounded_historical_delta64_value_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME delta_interval /\
    bounded_delta64_pair_products_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME delta_products /\
    bounded_delta64_gradient_from_products delta_products =
      SOME delta_gradient
Proof
  mp_tac registered_case10173_historical_center_specialized_first_named
  >> simp
       [registered_case10173_historical_center_reciprocals_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
        compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> strip_tac
  >> qpat_x_assum
       `SOME (value,gradient) =
        bounded_historical_dihedral_first64_decimal _ _ _ _`
       (fn th => assume_tac (GSYM th))
  >> drule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
  >> strip_tac
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_delta_gradient_exact_eval:
  100 < clock ==>
  ?gradient.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) =
      (M_success
        (from_cv (bounded_interval64_object_cv_list gradient)),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_delta_source_values
  >> strip_tac
  >> qexists_tac `delta_gradient`
  >> irule
       compute_registeredCase10173HistoricalDeltaCenterEvalTheory.registered_case10173_historical_center_delta_gradient_eval
  >> conj_tac
  >- simp []
  >> irule registered_case10173_historical_center_delta_gradient_matches
  >> simp []
QED

Theorem registered_case10173_historical_center_delta_value_closed_eval:
  100 < clock ==>
  ?value.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv value),refs)
Proof
  strip_tac
  >> mp_tac
       compute_registeredCase10173HistoricalDeltaCenterEvalTheory.registered_case10173_historical_center_delta_value_local_object
  >> strip_tac
  >> qexists_tac `value`
  >> irule
       compute_registeredCase10173HistoricalDeltaCenterEvalTheory.registered_case10173_historical_center_delta_value_eval
  >> simp []
QED

Theorem registered_case10173_historical_center_delta_gradient_closed_eval:
  100 < clock ==>
  ?gradient.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv gradient),refs)
Proof
  strip_tac
  >> mp_tac
       compute_registeredCase10173HistoricalDeltaCenterEvalTheory.registered_case10173_historical_center_delta_gradient_local_object
  >> strip_tac
  >> qexists_tac `registered_case10173_cv_list [g0;g1;g2;g3;g4;g5]`
  >> irule
       compute_registeredCase10173HistoricalDeltaCenterEvalTheory.registered_case10173_historical_center_delta_gradient_eval
  >> simp []
QED

Theorem registered_case10173_historical_center_u126_closed_eval:
  100 < clock ==>
  ?result.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  strip_tac
  >> mp_tac
       compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_u126_local_object
  >> strip_tac
  >> qexists_tac
       `Pair value
          (registered_case10173_cv_list
            [g0;g1;registered_case10173_interval_zero_cv;
             registered_case10173_interval_zero_cv;
             registered_case10173_interval_zero_cv;g2])`
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_u126_eval
  >> simp []
QED

Theorem registered_case10173_historical_center_u135_closed_eval:
  100 < clock ==>
  ?result.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  strip_tac
  >> mp_tac
       compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_u135_local_object
  >> strip_tac
  >> qexists_tac
       `Pair value
          (registered_case10173_cv_list
            [g0;registered_case10173_interval_zero_cv;g1;
             registered_case10173_interval_zero_cv;g2;
             registered_case10173_interval_zero_cv])`
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_u135_eval
  >> simp []
QED

Theorem registered_case10173_historical_center_u126_object_source_exact:
  registered_case10173_fs_hist_u126_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 =
    bounded_object_fs_historical_u126_decimal
      registered_case10173_historical_center_environment_decimal
Proof
  simp
    [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x0_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x1_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x2_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x3_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x4_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x5_def,
     registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_center_u135_object_source_exact:
  registered_case10173_fs_hist_u135_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 =
    bounded_object_fs_historical_u135_decimal
      registered_case10173_historical_center_environment_decimal
Proof
  simp
    [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x0_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x1_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x2_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x3_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x4_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x5_def,
     registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_center_u_source_values:
  ?u126 u126_gradient u135 u135_gradient.
    bounded_historical_u126_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME (u126,u126_gradient) /\
    bounded_historical_u135_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME (u135,u135_gradient)
Proof
  mp_tac registered_case10173_historical_center_specialized_first_named
  >> simp
       [registered_case10173_historical_center_reciprocals_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
        compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> strip_tac
  >> qpat_x_assum
       `SOME (value,gradient) =
        bounded_historical_dihedral_first64_decimal _ _ _ _`
       (fn th => assume_tac (GSYM th))
  >> drule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
  >> strip_tac
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_u126_exact_eval:
  100 < clock ==>
  ?value gradient.
    bounded_historical_u126_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME (value,gradient) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv value)
            (bounded_interval64_object_cv_list gradient))),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_u_source_values
  >> strip_tac
  >> qexists_tac `u126`
  >> qexists_tac `u126_gradient`
  >> conj_tac >- simp []
  >> `bounded_object_fs_historical_u126_decimal
        registered_case10173_historical_center_environment_decimal =
      SOME
        (Pair (bounded_interval64_object_cv u126)
          (bounded_interval64_object_cv_list u126_gradient))` by
       metis_tac
         [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_historical_u126_decimal_exact]
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u126_complete_object_eval
  >> simp [registered_case10173_historical_center_u126_object_source_exact]
QED

Theorem registered_case10173_historical_center_u135_exact_eval:
  100 < clock ==>
  ?value gradient.
    bounded_historical_u135_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME (value,gradient) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv value)
            (bounded_interval64_object_cv_list gradient))),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_u_source_values
  >> strip_tac
  >> qexists_tac `u135`
  >> qexists_tac `u135_gradient`
  >> conj_tac >- simp []
  >> `bounded_object_fs_historical_u135_decimal
        registered_case10173_historical_center_environment_decimal =
      SOME
        (Pair (bounded_interval64_object_cv u135)
          (bounded_interval64_object_cv_list u135_gradient))` by
       metis_tac
         [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_historical_u135_decimal_exact]
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u135_complete_object_eval
  >> simp [registered_case10173_historical_center_u135_object_source_exact]
QED

Theorem registered_case10173_historical_center_delta_x4_value_local_trace:
  ?negative_x0 negative_x3 linear p12 p03 p14 p25 p45 p0l
   negative_p12 negative_p03 negative_p45 result source_value.
    bounded_object_fs_interval_neg
      registered_case10173_historical_center_x0 = SOME negative_x0 /\
    bounded_object_fs_interval_neg
      registered_case10173_historical_center_x3 = SOME negative_x3 /\
    registered_case10173_fs_interval_sum_object
      [negative_x0;registered_case10173_historical_center_x1;
       registered_case10173_historical_center_x2;negative_x3;
       registered_case10173_historical_center_x4;
       registered_case10173_historical_center_x5] = SOME linear /\
    bounded_object_fs_interval_mul_decimal
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2 = SOME p12 /\
    bounded_object_fs_interval_mul_decimal
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x3 = SOME p03 /\
    bounded_object_fs_interval_mul_decimal
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x4 = SOME p14 /\
    bounded_object_fs_interval_mul_decimal
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x5 = SOME p25 /\
    bounded_object_fs_interval_mul_decimal
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 = SOME p45 /\
    bounded_object_fs_interval_mul_decimal
      registered_case10173_historical_center_x0 linear = SOME p0l /\
    bounded_object_fs_interval_neg p12 = SOME negative_p12 /\
    bounded_object_fs_interval_neg p03 = SOME negative_p03 /\
    bounded_object_fs_interval_neg p45 = SOME negative_p45 /\
    registered_case10173_fs_interval_sum_object
      [negative_p12;negative_p03;p14;p25;negative_p45;p0l] = SOME result /\
    bounded_historical_delta_x4_value_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME source_value /\
    result = bounded_interval64_object_cv source_value
Proof
  simp
    [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x0_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x1_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x2_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x3_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x4_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x5_def,
     registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_neg_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_def]
  >> EVAL_TAC
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_mul_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_neg_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_def]
  >> EVAL_TAC
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def]
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_x4_value_exact_eval:
  100 < clock ==>
  ?value.
    bounded_historical_delta_x4_value_decimal
      registered_case10173_historical_center_environment_decimal =
      SOME value /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) =
      (M_success (from_cv (bounded_interval64_object_cv value)),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_delta_x4_value_local_trace
  >> strip_tac
  >> qexists_tac `source_value`
  >> conj_tac >- simp []
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_hist_delta_x4_value_trace_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_delta_x4_value_eval:
  100 < clock ==>
  ?result.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_value»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_delta_x4_value_local_trace
  >> strip_tac
  >> qexists_tac `result`
  >> simp
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_hist_delta_x4_value_trace_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_center_delta_x4_gradient_local_trace:
  ?negative_two_x0 negative_two_x3 negative_x2 negative_x1
   negative_x5 negative_x4 g0 g1 g2 g4 g5 source_gradient.
    registered_case10173_fs_interval_scale_neg_two_object
      registered_case10173_historical_center_x0 = SOME negative_two_x0 /\
    registered_case10173_fs_interval_scale_neg_two_object
      registered_case10173_historical_center_x3 = SOME negative_two_x3 /\
    bounded_object_fs_interval_neg
      registered_case10173_historical_center_x2 = SOME negative_x2 /\
    bounded_object_fs_interval_neg
      registered_case10173_historical_center_x1 = SOME negative_x1 /\
    bounded_object_fs_interval_neg
      registered_case10173_historical_center_x5 = SOME negative_x5 /\
    bounded_object_fs_interval_neg
      registered_case10173_historical_center_x4 = SOME negative_x4 /\
    registered_case10173_fs_interval_sum_object
      [negative_two_x0;registered_case10173_historical_center_x1;
       registered_case10173_historical_center_x2;negative_two_x3;
       registered_case10173_historical_center_x4;
       registered_case10173_historical_center_x5] = SOME g0 /\
    registered_case10173_fs_interval_sum_object
      [registered_case10173_historical_center_x0;negative_x2;
       registered_case10173_historical_center_x4] = SOME g1 /\
    registered_case10173_fs_interval_sum_object
      [registered_case10173_historical_center_x0;negative_x1;
       registered_case10173_historical_center_x5] = SOME g2 /\
    registered_case10173_fs_interval_sum_object
      [registered_case10173_historical_center_x0;
       registered_case10173_historical_center_x1;negative_x5] = SOME g4 /\
    registered_case10173_fs_interval_sum_object
      [registered_case10173_historical_center_x0;
       registered_case10173_historical_center_x2;negative_x4] = SOME g5 /\
    bounded_historical_delta_x4_gradient
      registered_case10173_historical_center_environment_decimal =
      SOME source_gradient /\
    registered_case10173_cv_list [g0;g1;g2;negative_two_x0;g4;g5] =
      bounded_interval64_object_cv_list source_gradient
Proof
  simp
    [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x0_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x1_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x2_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x3_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x4_def,
     compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_x5_def,
     registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def,
     compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_scale_neg_two_object_def,
     compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_sum_object_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_neg_def,
     compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_def]
  >> EVAL_TAC
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_canonical_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem registered_case10173_historical_center_delta_x4_gradient_exact_eval:
  100 < clock ==>
  ?gradient.
    bounded_historical_delta_x4_gradient
      registered_case10173_historical_center_environment_decimal =
      SOME gradient /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_gradient»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) =
      (M_success (from_cv (bounded_interval64_object_cv_list gradient)),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_delta_x4_gradient_local_trace
  >> strip_tac
  >> qexists_tac `source_gradient`
  >> conj_tac >- simp []
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> qpat_x_assum
       `registered_case10173_cv_list
          [g0;g1;g2;negative_two_x0;g4;g5] =
        bounded_interval64_object_cv_list source_gradient`
       (fn th => once_rewrite_tac [GSYM th])
  >> irule
       compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_hist_delta_x4_gradient_trace_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_delta_x4_gradient_eval:
  100 < clock ==>
  ?gradient.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_delta_x4_gradient»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv gradient),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_delta_x4_gradient_local_trace
  >> strip_tac
  >> qexists_tac
       `registered_case10173_cv_list
          [g0;g1;g2;negative_two_x0;g4;g5]`
  >> once_rewrite_tac
       [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_hist_delta_x4_gradient_trace_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_root_scale2_object_exact:
  ?twice_root_delta.
    bounded_historical_scale2
      registered_case10173_historical_center_root_delta =
      SOME twice_root_delta /\
    registered_case10173_fs_interval_raw_scale_object 2
      (bounded_interval64_object_cv
        registered_case10173_historical_center_root_delta) =
      SOME (bounded_interval64_object_cv twice_root_delta)
Proof
  simp
    [registered_case10173_historical_center_root_delta_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def,
     compute_boundedIntervalAddTheory.bounded_interval64_add_def,
     compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def,
     compute_boundedIntervalTheory.bounded_interval64_valid_def,
     compute_boundedSignedEndpointAddTheory.bounded_signed64_add_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_widen128_def,
     compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
     compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def,
     compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> qexists_tac
       `BoundedInterval64
          (BoundedSigned64 F 23875893153484w)
          (BoundedSigned64 F 23875893153552w)`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

Theorem registered_case10173_fs_hist_positive_inv_after_scale2_eval:
  registered_case10173_fs_interval_raw_scale_object 2
      (bounded_interval64_object_cv input) =
      SOME (bounded_interval64_object_cv twice) /\
  bounded_interval64_positive_inv_certificate_decimal twice output /\
  12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;from_cv (bounded_interval64_object_cv input)]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv output)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_positive_inv»
            [from_cv (bounded_interval64_object_cv twice)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_center_root_reciprocal_trace:
  ?twice_root_delta.
    bounded_historical_scale2
      registered_case10173_historical_center_root_delta =
      SOME twice_root_delta /\
    bounded_interval64_positive_inv_certificate_decimal
      twice_root_delta
      registered_case10173_historical_center_root_derivative /\
    bounded_interval64_positive_inv_certificate_decimal
      twice_root_delta
      registered_case10173_historical_center_special_root_reciprocal /\
    bounded_interval64_positive_inv_certificate_decimal
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_root_four_reciprocal
Proof
  mp_tac registered_case10173_historical_center_specialized_first_named
  >> simp [registered_case10173_historical_center_reciprocals_components]
  >> strip_tac
  >> qpat_x_assum
       `SOME (value,gradient) =
        bounded_historical_dihedral_first64_decimal _ _ _ _`
       (fn th => assume_tac (GSYM th))
  >> drule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
  >> strip_tac
  >> metis_tac []
QED

Theorem registered_case10173_historical_center_root_derivative_eval:
  120 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;
           from_cv
             (bounded_interval64_object_cv
               registered_case10173_historical_center_root_delta)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          registered_case10173_historical_center_root_derivative)),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_root_scale2_object_exact
  >> mp_tac registered_case10173_historical_center_root_reciprocal_trace
  >> strip_tac
  >> strip_tac
  >> gvs []
  >> irule registered_case10173_fs_hist_positive_inv_after_scale2_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `twice_root_delta`
  >> simp []
QED

Theorem registered_case10173_historical_center_special_root_reciprocal_eval:
  120 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;
           from_cv
             (bounded_interval64_object_cv
               registered_case10173_historical_center_root_delta)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          registered_case10173_historical_center_special_root_reciprocal)),
     refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_root_scale2_object_exact
  >> mp_tac registered_case10173_historical_center_root_reciprocal_trace
  >> strip_tac
  >> strip_tac
  >> gvs []
  >> irule registered_case10173_fs_hist_positive_inv_after_scale2_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `twice_root_delta`
  >> simp []
QED

Theorem registered_case10173_historical_center_root_four_reciprocal_eval:
  120 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [from_cv
          (bounded_interval64_object_cv
            registered_case10173_historical_center_root_four_x0)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          registered_case10173_historical_center_root_four_reciprocal)),
     refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_root_reciprocal_trace
  >> strip_tac
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_list_scale_decimal_length:
  !scalar values result.
    bounded_interval64_list_scale_decimal scalar values = SOME result ==>
    LENGTH result = LENGTH values
Proof
  Induct_on `values`
  >> simp
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def]
  >> rpt strip_tac
  >> every_case_tac
  >> gvs []
  >> res_tac
QED

Theorem bounded_delta64_gradient_from_products_length:
  !products gradient.
    bounded_delta64_gradient_from_products products = SOME gradient ==>
    LENGTH gradient = 6
Proof
  rpt gen_tac
  >> simp
       [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def,
        compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def]
  >> every_case_tac
  >> rpt strip_tac
  >> gvs []
QED

Theorem bounded_historical_delta_x4_gradient_length:
  !environment result.
    bounded_historical_delta_x4_gradient environment = SOME result ==>
    LENGTH result = 6
Proof
  rpt gen_tac
  >> simp
       [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def]
  >> every_case_tac
  >> rpt strip_tac
  >> gvs []
QED

Theorem bounded_interval64_list_add_at_length:
  !value index values result.
    bounded_interval64_list_add_at value index values = SOME result ==>
    LENGTH result = LENGTH values
Proof
  Induct_on `values`
  >> Cases_on `index`
  >> simp
       [compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def]
  >> rpt strip_tac
  >> every_case_tac
  >> gvs []
  >> res_tac
QED

Theorem bounded_historical_c_vector_decimal_lengths:
  !delta_x4 b delta_gradient b_gradient result.
    bounded_historical_c_vector_decimal delta_x4 b
      delta_gradient b_gradient = SOME result ==>
    LENGTH result = LENGTH delta_gradient /\
    LENGTH result = LENGTH b_gradient
Proof
  Induct_on `delta_gradient`
  >> Cases_on `b_gradient`
  >> simp
       [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_c_vector_decimal_def]
  >> rpt strip_tac
  >> every_case_tac
  >> gvs []
  >> res_tac
QED

Theorem length_six_cases:
  !values.
    LENGTH values = 6 ==>
    ?v0 v1 v2 v3 v4 v5. values = [v0;v1;v2;v3;v4;v5]
Proof
  Cases_on `values` >> simp []
  >> Cases_on `t` >> simp []
  >> Cases_on `t'` >> simp []
  >> Cases_on `t` >> simp []
  >> Cases_on `t'` >> simp []
  >> Cases_on `t` >> simp []
  >> Cases_on `t'` >> simp []
QED

Theorem registered_case10173_fs_hist_c_vector_object_cons:
  !delta_x4 b delta_gradient delta_rest b_gradient b_rest result rest.
    bounded_object_fs_historical_c_vector_decimal delta_x4 b
      (Pair delta_gradient delta_rest) (Pair b_gradient b_rest) =
      SOME (Pair result rest) ==>
    registered_case10173_fs_hist_c_entry_object delta_x4 b
      delta_gradient b_gradient = SOME result /\
    bounded_object_fs_historical_c_vector_decimal delta_x4 b
      delta_rest b_rest = SOME rest
Proof
  rw
    [compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_historical_c_vector_decimal_def,
     compute_registeredCase10173HistoricalCVectorEvalTheory.registered_case10173_fs_hist_c_entry_object_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_fs_hist_c_vector_six_typed_eval:
  !delta_x4 b delta_gradient b_gradient result clock refs.
    LENGTH delta_gradient = 6 /\
    LENGTH b_gradient = 6 /\
    bounded_historical_c_vector_decimal delta_x4 b
      delta_gradient b_gradient = SOME result /\
    18 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_c_vector»
        [from_cv (bounded_interval64_object_cv delta_x4);
         from_cv (bounded_interval64_object_cv b);
         from_cv (bounded_interval64_object_cv_list delta_gradient);
         from_cv (bounded_interval64_object_cv_list b_gradient)])
      refs =
    (M_success
      (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> `?d0 d1 d2 d3 d4 d5.
        delta_gradient = [d0;d1;d2;d3;d4;d5]` by
       metis_tac [length_six_cases]
  >> `?b0 b1 b2 b3 b4 b5.
        b_gradient = [b0;b1;b2;b3;b4;b5]` by
       metis_tac [length_six_cases]
  >> `LENGTH result = 6` by
       metis_tac [bounded_historical_c_vector_decimal_lengths]
  >> `?c0 c1 c2 c3 c4 c5.
        result = [c0;c1;c2;c3;c4;c5]` by
       metis_tac [length_six_cases]
  >> gvs []
  >> drule
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_historical_c_vector_decimal_exact
  >> strip_tac
  >> fs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> imp_res_tac registered_case10173_fs_hist_c_vector_object_cons
  >> imp_res_tac registered_case10173_fs_hist_c_vector_object_cons
  >> imp_res_tac registered_case10173_fs_hist_c_vector_object_cons
  >> imp_res_tac registered_case10173_fs_hist_c_vector_object_cons
  >> imp_res_tac registered_case10173_fs_hist_c_vector_object_cons
  >> imp_res_tac registered_case10173_fs_hist_c_vector_object_cons
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
          compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
         compute_registeredCase10173HistoricalCVectorEvalTheory.registered_case10173_fs_hist_c_vector_six_eval)
  >> simp []
QED

Theorem registered_case10173_fs_hist_b_gradient_six_typed_eval:
  !base correction result correction_expression clock refs.
    LENGTH base = 6 /\
    bounded_interval64_list_add_at correction 0 base = SOME result /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      correction_expression refs =
      (M_success
        (from_cv (bounded_interval64_object_cv correction)),refs) /\
    20 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_interval_add»
           [App «candle_cv_fs_interval_lookup»
              [Num 0;from_cv (bounded_interval64_object_cv_list base)];
            correction_expression];
         App «candle_cv_fs_interval_lookup»
           [Num 1;from_cv (bounded_interval64_object_cv_list base)];
         App «candle_cv_fs_interval_lookup»
           [Num 2;from_cv (bounded_interval64_object_cv_list base)];
         App «candle_cv_fs_interval_lookup»
           [Num 3;from_cv (bounded_interval64_object_cv_list base)];
         App «candle_cv_fs_interval_lookup»
           [Num 4;from_cv (bounded_interval64_object_cv_list base)];
         App «candle_cv_fs_interval_lookup»
           [Num 5;from_cv (bounded_interval64_object_cv_list base)]])
      refs =
    (M_success
      (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> `?v0 v1 v2 v3 v4 v5.
        base = [v0;v1;v2;v3;v4;v5]` by
       metis_tac [length_six_cases]
  >> gvs []
  >> `?updated.
        bounded_interval64_add v0 correction = SOME updated /\
        result = [updated;v1;v2;v3;v4;v5]` by
       (qpat_x_assum
          `bounded_interval64_list_add_at correction 0
             [v0;v1;v2;v3;v4;v5] = SOME result`
          mp_tac
        >> simp
             [compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def]
        >> TOP_CASE_TAC
        >> gvs [])
  >> gvs []
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv (bounded_interval64_object_cv updated);
             from_cv (bounded_interval64_object_cv v1);
             from_cv (bounded_interval64_object_cv v2);
             from_cv (bounded_interval64_object_cv v3);
             from_cv (bounded_interval64_object_cv v4);
             from_cv (bounded_interval64_object_cv v5)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> rpt conj_tac
      >- intLib.ARITH_TAC
      >- (irule
            compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
          >> conj_tac
          >- intLib.ARITH_TAC
          >> qexists_tac `bounded_interval64_object_cv v0`
          >> qexists_tac `bounded_interval64_object_cv correction`
          >> conj_tac
          >- (irule
                compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
              >> simp [])
          >> conj_tac
          >- (irule
                (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
                  (Q.SPECL
                    [`0`,`[v0;v1;v2;v3;v4;v5]`,`clock`,`refs`]
                    compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
              >> simp []
              >> intLib.ARITH_TAC)
          >> simp [])
      >- (irule
            (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
              (Q.SPECL [`1`,`[v0;v1;v2;v3;v4;v5]`,`clock`,`refs`]
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
          >> simp []
          >> intLib.ARITH_TAC)
      >- (irule
            (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
              (Q.SPECL [`2`,`[v0;v1;v2;v3;v4;v5]`,`clock`,`refs`]
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
          >> simp []
          >> intLib.ARITH_TAC)
      >- (irule
            (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
              (Q.SPECL [`3`,`[v0;v1;v2;v3;v4;v5]`,`clock`,`refs`]
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
          >> simp []
          >> intLib.ARITH_TAC)
      >- (irule
            (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
              (Q.SPECL [`4`,`[v0;v1;v2;v3;v4;v5]`,`clock`,`refs`]
                compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule
           (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
             (Q.SPECL [`5`,`[v0;v1;v2;v3;v4;v5]`,`clock`,`refs`]
               compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_execTheory.from_cv_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_list_scale_typed_eval:
  !scalar values result clock refs.
    LENGTH values = 6 /\
    bounded_interval64_list_scale_decimal scalar values = SOME result /\
    20 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv (bounded_interval64_object_cv scalar);
         from_cv (bounded_interval64_object_cv_list values)]) refs =
    (M_success
      (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_fsn_interval_list_scale_bounded_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> irule
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> first_assum ACCEPT_TAC
QED

Theorem bounded_interval64_atan_range_none_is_unit:
  !input result.
    bounded_interval64_atan_range_decimal input NONE NONE = SOME result ==>
    bounded_interval64_atan_unit_decimal input = SOME result
Proof
  Cases_on `input`
  >> simp
       [compute_boundedAtanDecimalTheory.bounded_interval64_atan_range_decimal_def]
  >> simp
       [compute_boundedAtanDecimalTheory.bounded_interval64_atan_range_point_decimal_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        LET_THM]
  >> simp
       [compute_boundedAtanDecimalTheory.bounded_interval64_atan_unit_decimal_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        LET_THM]
  >> every_case_tac
  >> gvs
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem registered_case10173_historical_final_value_typed_eval:
  !quotient angle value clock refs.
    bounded_interval64_atan_range_decimal quotient NONE NONE = SOME angle /\
    bounded_interval64_add bounded_historical_pi_half_decimal angle =
      SOME value /\
    50 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_interval_of_q»
           [App «candle_cv_q_pi_half_interval» []];
         App «candle_cv_fs_hist_atan_interval»
           [from_cv (bounded_interval64_object_cv quotient)]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv value)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_interval64_object_cv bounded_historical_pi_half_decimal`
  >> qexists_tac `bounded_interval64_object_cv angle`
  >> conj_tac
  >- (irule
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
      >> simp [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_pi_half_interval_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalAtanIntervalEvalTheory.registered_case10173_fs_hist_atan_interval_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> irule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_interval64_atan_unit_decimal_exact
  >> irule bounded_interval64_atan_range_none_is_unit
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_fs_interval_mul_typed_eval:
  !left right result clock refs.
    bounded_interval64_mul_decimal left right = SOME result /\
    15 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv (bounded_interval64_object_cv left);
         from_cv (bounded_interval64_object_cv right)]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> irule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_historical_special_gradient_typed_eval:
  !result clock refs.
    bounded_interval64_mul_decimal
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_special_root_reciprocal =
      SOME result /\
    140 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv
           (bounded_interval64_object_cv
             registered_case10173_historical_center_root_four_x0);
         App «candle_cv_fs_hist_positive_inv»
           [App «candle_cv_fs_angle_interval_scale»
             [Num 2;
              from_cv
                (bounded_interval64_object_cv
                  registered_case10173_historical_center_root_delta)]]])
      refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_center_root_four_x0`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_center_special_root_reciprocal`
  >> conj_tac
  >- (irule
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
      >> first_assum ACCEPT_TAC)
  >> conj_tac
  >- simp [compute_execProofTheory.compute_eval_from_cv]
  >> irule registered_case10173_historical_center_special_root_reciprocal_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_quotient_typed_eval:
  !delta_x4 b b_reciprocal quotient clock refs.
    bounded_interval64_mul_decimal (bounded_interval64_neg delta_x4)
      b_reciprocal = SOME quotient /\
    bounded_interval64_positive_inv_certificate_decimal b b_reciprocal /\
    30 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_neg»
           [from_cv (bounded_interval64_object_cv delta_x4)];
         App «candle_cv_fs_hist_positive_inv»
           [from_cv (bounded_interval64_object_cv b)]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv quotient)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_interval64_object_cv (bounded_interval64_neg delta_x4)`
  >> qexists_tac `bounded_interval64_object_cv b_reciprocal`
  >> conj_tac
  >- (irule
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
      >> first_assum ACCEPT_TAC)
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
      >> conj_tac
      >- intLib.ARITH_TAC
      >> irule
           compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact)
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qpat_x_assum
       `bounded_interval64_positive_inv_certificate_decimal b b_reciprocal`
       ACCEPT_TAC
QED

Theorem registered_case10173_atan_one_scale2_object_exact:
  !two.
    bounded_historical_scale2 bounded_atan_one_decimal = SOME two ==>
    registered_case10173_fs_interval_raw_scale_object 2
      (bounded_interval64_object_cv bounded_atan_one_decimal) =
    SOME (bounded_interval64_object_cv two)
Proof
  simp
    [compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def,
     compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def,
     compute_boundedIntervalAddTheory.bounded_interval64_add_def,
     compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def,
     compute_boundedIntervalTheory.bounded_interval64_valid_def,
     compute_boundedSignedEndpointAddTheory.bounded_signed64_add_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_widen128_def,
     compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
     compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def,
     compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> rpt strip_tac
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

Theorem registered_case10173_atan_one_scale2_typed_eval:
  !two clock refs.
    bounded_historical_scale2 bounded_atan_one_decimal = SOME two /\
    10 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [Num 2;App «candle_cv_fs_interval_one» []]) refs =
    (M_success (from_cv (bounded_interval64_object_cv two)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_scale»
            [from_cv (Num 2);
             from_cv
               (bounded_interval64_object_cv bounded_atan_one_decimal)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def,
            compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
            compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_one_eval)
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_object_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> irule registered_case10173_atan_one_scale2_object_exact
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_historical_two_over_root_four_typed_eval:
  !two result clock refs.
    bounded_historical_scale2 bounded_atan_one_decimal = SOME two /\
    bounded_interval64_mul_decimal two
      registered_case10173_historical_center_root_four_reciprocal =
      SOME result /\
    140 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_angle_interval_scale»
           [Num 2;App «candle_cv_fs_interval_one» []];
         App «candle_cv_fs_hist_positive_inv»
           [from_cv
             (bounded_interval64_object_cv
               registered_case10173_historical_center_root_four_x0)]])
      refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv two`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_center_root_four_reciprocal`
  >> conj_tac
  >- (irule
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
      >> qpat_x_assum
           `bounded_interval64_mul_decimal two _ = SOME result`
           ACCEPT_TAC)
  >> conj_tac
  >- (irule registered_case10173_atan_one_scale2_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_historical_center_root_four_reciprocal_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_reciprocal_u_typed_eval:
  !u126 u126_gradient u135 u135_gradient u_product clock refs.
    bounded_interval64_mul_decimal u126 u135 = SOME u_product /\
    bounded_interval64_positive_inv_certificate_decimal u_product
      registered_case10173_historical_center_u_reciprocal /\
    40 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [App «candle_cv_fs_angle_interval_mul»
          [Uop Fst
             (from_cv
               (Pair (bounded_interval64_object_cv u126)
                 (bounded_interval64_object_cv_list u126_gradient)));
           Uop Fst
             (from_cv
               (Pair (bounded_interval64_object_cv u135)
                 (bounded_interval64_object_cv_list u135_gradient)))]])
      refs =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          registered_case10173_historical_center_u_reciprocal)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_positive_inv»
            [from_cv (bounded_interval64_object_cv u_product)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac
      >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
      >> conj_tac
      >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_object_cv u126`
      >> qexists_tac `bounded_interval64_object_cv u135`
      >> conj_tac
      >- (irule
            compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
          >> qpat_x_assum
               `bounded_interval64_mul_decimal u126 u135 = SOME u_product`
               ACCEPT_TAC)
      >> conj_tac
      >- simp
           [compute_execTheory.from_cv_def,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
      >> simp
           [compute_execTheory.from_cv_def,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> conj_tac
  >- intLib.ARITH_TAC
  >> qpat_x_assum
       `bounded_interval64_positive_inv_certificate_decimal u_product
          registered_case10173_historical_center_u_reciprocal`
       ACCEPT_TAC
QED

Theorem registered_case10173_historical_center_first_order_exact_eval:
  200 < clock ==>
  ?value gradient.
    bounded_historical_dihedral_first64_decimal
      registered_case10173_historical_center_environment_decimal
      registered_case10173_historical_center_root_delta
      registered_case10173_historical_center_root_four_x0
      [registered_case10173_historical_center_root_derivative;
       registered_case10173_historical_center_root_four_reciprocal;
       registered_case10173_historical_center_u_reciprocal;
       registered_case10173_historical_center_special_root_reciprocal;
       registered_case10173_historical_center_b_reciprocal] =
      SOME (value,gradient) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv registered_case10173_historical_center_environment_object;
         from_cv
           (bounded_interval64_object_cv
             registered_case10173_historical_center_root_delta);
         from_cv
           (bounded_interval64_object_cv
             registered_case10173_historical_center_root_four_x0)])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv value)
            (bounded_interval64_object_cv_list gradient))),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_center_specialized_first_named
  >> simp [registered_case10173_historical_center_reciprocals_components]
  >> strip_tac
  >> qpat_x_assum
       `SOME (value,gradient) =
        bounded_historical_dihedral_first64_decimal _ _ _ _`
       (fn th => assume_tac (GSYM th))
  >> drule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
  >> strip_tac
  >> `LENGTH delta_gradient = 6` by
       metis_tac [bounded_delta64_gradient_from_products_length]
  >> `LENGTH root_gradient = 6` by
       metis_tac [bounded_interval64_list_scale_decimal_length]
  >> `LENGTH delta_x4_gradient = 6` by
       metis_tac [bounded_historical_delta_x4_gradient_length]
  >> `LENGTH b_gradient_base = 6` by
       metis_tac [bounded_interval64_list_scale_decimal_length]
  >> `LENGTH b_gradient = 6` by
       metis_tac [bounded_interval64_list_add_at_length]
  >> `LENGTH c = 6` by
       metis_tac [bounded_historical_c_vector_decimal_lengths]
  >> qexists_tac `value`
  >> qexists_tac `gradient`
  >> conj_tac >- simp []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalFirstOrderEvalTheory.registered_case10173_fs_hist_first_order_composition_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (mp_tac
        (Q.INST [`clock` |-> `clock - 1`]
          registered_case10173_historical_center_delta_value_closed_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> simp [])
  >> qexists_tac `bounded_interval64_object_cv b`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient_base`
  >> qexists_tac `bounded_interval64_object_cv_list c`
  >> qexists_tac `bounded_interval64_object_cv_list delta_gradient`
  >> qexists_tac `bounded_interval64_object_cv_list delta_x4_gradient`
  >> qexists_tac `bounded_interval64_object_cv delta_x4`
  >> qexists_tac `bounded_interval64_object_cv_list gradient_base`
  >> qexists_tac `bounded_interval64_object_cv quotient`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_center_u_reciprocal`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_center_root_derivative`
  >> qexists_tac `bounded_interval64_object_cv_list root_gradient`
  >> qexists_tac `bounded_interval64_object_cv special_gradient`
  >> qexists_tac `bounded_interval64_object_cv two_over_root_four`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u126)
          (bounded_interval64_object_cv_list u126_gradient)`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u135)
          (bounded_interval64_object_cv_list u135_gradient)`
  >> rpt conj_tac
  >- (mp_tac
        (Q.INST [`clock` |-> `clock - 7`]
          registered_case10173_historical_center_u126_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> gvs [])
  >- (mp_tac
        (Q.INST [`clock` |-> `clock - 8`]
          registered_case10173_historical_center_u135_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> gvs [])
  >- (irule registered_case10173_historical_final_value_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_center_root_derivative_eval
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac
        compute_registeredCase10173HistoricalDeltaCenterEvalTheory.registered_case10173_historical_center_delta_gradient_eval
      >> conj_tac
      >- (irule registered_case10173_historical_center_delta_gradient_matches
          >> simp [])
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (mp_tac
        (Q.INST [`clock` |-> `clock - 5`]
          registered_case10173_historical_center_delta_x4_value_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> gvs [])
  >- (irule registered_case10173_fs_interval_mul_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_hist_replace_three_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_fs_hist_c_vector_six_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_special_gradient_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac registered_case10173_fs_hist_b_gradient_six_typed_eval
      >> qexists_tac `b_correction`
      >> rpt conj_tac
      >- simp []
      >- simp []
      >- (irule registered_case10173_fs_interval_mul_typed_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >- (mp_tac
        (Q.INST [`clock` |-> `clock - 6`]
          registered_case10173_historical_center_delta_x4_gradient_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> gvs [])
  >- (irule
        registered_case10173_historical_two_over_root_four_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac registered_case10173_historical_quotient_typed_eval
      >> qexists_tac
           `registered_case10173_historical_center_b_reciprocal`
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_historical_reciprocal_u_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
