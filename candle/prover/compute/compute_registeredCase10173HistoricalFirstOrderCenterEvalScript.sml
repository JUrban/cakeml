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

val _ = export_theory ();
