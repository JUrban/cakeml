(*****************************************************************************
 * Closed registered second-order evaluation for the authenticated genuine
 * case-10173 box packet.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderBoxEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderEval
  compute_registeredCase10173HistoricalUObjectEmbeddingEval
  compute_boundedCase10173HistoricalCellDecimalBoundary
Libs
  bossLib preamble wordsLib

Definition registered_case10173_historical_box_environment_decimal_def:
  registered_case10173_historical_box_environment_decimal =
    bounded_case10173_packet_box_environment
      bounded_case10173_decimal_packet0_source_aligned
End

Definition registered_case10173_historical_box_root_delta_def:
  registered_case10173_historical_box_root_delta =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => box_root_delta
End

Definition registered_case10173_historical_box_root_four_x0_def:
  registered_case10173_historical_box_root_four_x0 =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => box_root_four_x0
End

Definition registered_case10173_historical_box_reciprocals_def:
  registered_case10173_historical_box_reciprocals =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => box_reciprocals
End

Definition registered_case10173_historical_box_root_derivative_def:
  registered_case10173_historical_box_root_derivative =
    EL 0 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_root_logarithmic_def:
  registered_case10173_historical_box_root_logarithmic =
    EL 1 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_root_four_reciprocal_def:
  registered_case10173_historical_box_root_four_reciprocal =
    EL 2 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_diagonal_reciprocal_def:
  registered_case10173_historical_box_diagonal_reciprocal =
    EL 3 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_u_reciprocal_def:
  registered_case10173_historical_box_u_reciprocal =
    EL 4 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_special_root_reciprocal_def:
  registered_case10173_historical_box_special_root_reciprocal =
    EL 5 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_b_reciprocal_def:
  registered_case10173_historical_box_b_reciprocal =
    EL 6 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_u126_reciprocal_def:
  registered_case10173_historical_box_u126_reciprocal =
    EL 7 registered_case10173_historical_box_reciprocals
End

Definition registered_case10173_historical_box_u135_reciprocal_def:
  registered_case10173_historical_box_u135_reciprocal =
    EL 8 registered_case10173_historical_box_reciprocals
End

Theorem registered_case10173_historical_box_specialized_second_exists:
  ?value gradient hessian.
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals =>
      bounded_historical_dihedral_second64_decimal box_environment
        box_root_delta box_root_four_x0 box_reciprocals =
      SOME (value,gradient,hessian)
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

Theorem registered_case10173_historical_box_specialized_second_named:
  ?value gradient hessian.
    bounded_historical_dihedral_second64_decimal
      registered_case10173_historical_box_environment_decimal
      registered_case10173_historical_box_root_delta
      registered_case10173_historical_box_root_four_x0
      registered_case10173_historical_box_reciprocals =
    SOME (value,gradient,hessian)
Proof
  mp_tac registered_case10173_historical_box_specialized_second_exists
  >> Cases_on `bounded_case10173_decimal_packet0_source_aligned`
  >> simp
       [registered_case10173_historical_box_environment_decimal_def,
        registered_case10173_historical_box_root_delta_def,
        registered_case10173_historical_box_root_four_x0_def,
        registered_case10173_historical_box_reciprocals_def,
        compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def]
  >> metis_tac []
QED

Theorem registered_case10173_historical_box_reciprocals_components:
  registered_case10173_historical_box_reciprocals =
    [registered_case10173_historical_box_root_derivative;
     registered_case10173_historical_box_root_logarithmic;
     registered_case10173_historical_box_root_four_reciprocal;
     registered_case10173_historical_box_diagonal_reciprocal;
     registered_case10173_historical_box_u_reciprocal;
     registered_case10173_historical_box_special_root_reciprocal;
     registered_case10173_historical_box_b_reciprocal;
     registered_case10173_historical_box_u126_reciprocal;
     registered_case10173_historical_box_u135_reciprocal]
Proof
  EVAL_TAC
QED

Definition registered_case10173_historical_box_x0_def:
  registered_case10173_historical_box_x0 =
    bounded_interval64_object_cv
      (EL 0 registered_case10173_historical_box_environment_decimal)
End

Definition registered_case10173_historical_box_x1_def:
  registered_case10173_historical_box_x1 =
    bounded_interval64_object_cv
      (EL 1 registered_case10173_historical_box_environment_decimal)
End

Definition registered_case10173_historical_box_x2_def:
  registered_case10173_historical_box_x2 =
    bounded_interval64_object_cv
      (EL 2 registered_case10173_historical_box_environment_decimal)
End

Definition registered_case10173_historical_box_x3_def:
  registered_case10173_historical_box_x3 =
    bounded_interval64_object_cv
      (EL 3 registered_case10173_historical_box_environment_decimal)
End

Definition registered_case10173_historical_box_x4_def:
  registered_case10173_historical_box_x4 =
    bounded_interval64_object_cv
      (EL 4 registered_case10173_historical_box_environment_decimal)
End

Definition registered_case10173_historical_box_x5_def:
  registered_case10173_historical_box_x5 =
    bounded_interval64_object_cv
      (EL 5 registered_case10173_historical_box_environment_decimal)
End

Definition registered_case10173_historical_box_environment_object_def:
  registered_case10173_historical_box_environment_object =
    registered_case10173_cv_list
      [registered_case10173_historical_box_x0;
       registered_case10173_historical_box_x1;
       registered_case10173_historical_box_x2;
       registered_case10173_historical_box_x3;
       registered_case10173_historical_box_x4;
       registered_case10173_historical_box_x5]
End

Theorem registered_case10173_historical_box_environment_object_exact:
  registered_case10173_historical_box_environment_object =
    bounded_interval64_object_cv_list
      registered_case10173_historical_box_environment_decimal
Proof
  simp
    [registered_case10173_historical_box_environment_object_def,
     registered_case10173_historical_box_x0_def,
     registered_case10173_historical_box_x1_def,
     registered_case10173_historical_box_x2_def,
     registered_case10173_historical_box_x3_def,
     registered_case10173_historical_box_x4_def,
     registered_case10173_historical_box_x5_def,
     registered_case10173_historical_box_environment_decimal_def,
     compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_historical_box_u126_object_source_exact:
  registered_case10173_fs_hist_u126_object
      registered_case10173_historical_box_x0
      registered_case10173_historical_box_x1
      registered_case10173_historical_box_x2
      registered_case10173_historical_box_x3
      registered_case10173_historical_box_x4
      registered_case10173_historical_box_x5 =
    bounded_object_fs_historical_u126_decimal
      registered_case10173_historical_box_environment_decimal
Proof
  simp
    [registered_case10173_historical_box_x0_def,
     registered_case10173_historical_box_x1_def,
     registered_case10173_historical_box_x2_def,
     registered_case10173_historical_box_x3_def,
     registered_case10173_historical_box_x4_def,
     registered_case10173_historical_box_x5_def,
     registered_case10173_historical_box_environment_decimal_def,
     compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_box_u135_object_source_exact:
  registered_case10173_fs_hist_u135_object
      registered_case10173_historical_box_x0
      registered_case10173_historical_box_x1
      registered_case10173_historical_box_x2
      registered_case10173_historical_box_x3
      registered_case10173_historical_box_x4
      registered_case10173_historical_box_x5 =
    bounded_object_fs_historical_u135_decimal
      registered_case10173_historical_box_environment_decimal
Proof
  simp
    [registered_case10173_historical_box_x0_def,
     registered_case10173_historical_box_x1_def,
     registered_case10173_historical_box_x2_def,
     registered_case10173_historical_box_x3_def,
     registered_case10173_historical_box_x4_def,
     registered_case10173_historical_box_x5_def,
     registered_case10173_historical_box_environment_decimal_def,
     compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_box_u_source_values:
  ?u126 u126_gradient u135 u135_gradient.
    bounded_historical_u126_decimal
      registered_case10173_historical_box_environment_decimal =
      SOME (u126,u126_gradient) /\
    bounded_historical_u135_decimal
      registered_case10173_historical_box_environment_decimal =
      SOME (u135,u135_gradient)
Proof
  mp_tac registered_case10173_historical_box_specialized_second_named
  >> simp [registered_case10173_historical_box_reciprocals_components]
  >> strip_tac
  >> qpat_x_assum
       `SOME (value,gradient,hessian) =
        bounded_historical_dihedral_second64_decimal _ _ _ _`
       (fn th => assume_tac (GSYM th))
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> metis_tac []
QED

Theorem registered_case10173_historical_box_u126_exact_eval:
  100 < clock ==>
  ?value gradient.
    bounded_historical_u126_decimal
      registered_case10173_historical_box_environment_decimal =
      SOME (value,gradient) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv registered_case10173_historical_box_environment_object])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv value)
            (bounded_interval64_object_cv_list gradient))),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_box_u_source_values
  >> strip_tac
  >> qexists_tac `u126`
  >> qexists_tac `u126_gradient`
  >> conj_tac >- simp []
  >> `bounded_object_fs_historical_u126_decimal
        registered_case10173_historical_box_environment_decimal =
      SOME
        (Pair (bounded_interval64_object_cv u126)
          (bounded_interval64_object_cv_list u126_gradient))` by
       metis_tac
         [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_historical_u126_decimal_exact]
  >> once_rewrite_tac [registered_case10173_historical_box_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u126_complete_object_eval
  >> simp [registered_case10173_historical_box_u126_object_source_exact]
QED

Theorem registered_case10173_historical_box_u135_exact_eval:
  100 < clock ==>
  ?value gradient.
    bounded_historical_u135_decimal
      registered_case10173_historical_box_environment_decimal =
      SOME (value,gradient) /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv registered_case10173_historical_box_environment_object])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (bounded_interval64_object_cv value)
            (bounded_interval64_object_cv_list gradient))),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_historical_box_u_source_values
  >> strip_tac
  >> qexists_tac `u135`
  >> qexists_tac `u135_gradient`
  >> conj_tac >- simp []
  >> `bounded_object_fs_historical_u135_decimal
        registered_case10173_historical_box_environment_decimal =
      SOME
        (Pair (bounded_interval64_object_cv u135)
          (bounded_interval64_object_cv_list u135_gradient))` by
       metis_tac
         [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_historical_u135_decimal_exact]
  >> once_rewrite_tac [registered_case10173_historical_box_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u135_complete_object_eval
  >> simp [registered_case10173_historical_box_u135_object_source_exact]
QED

Theorem registered_case10173_bounded_hessian64_rows_from_length:
  LENGTH hessian = 21 ==>
  ?rows.
    bounded_hessian64_rows hessian = SOME rows /\
    LENGTH rows = 6 /\ EVERY (\row. LENGTH row = 6) rows
Proof
  strip_tac
  >> fs
       [listTheory.LENGTH_EQ_NUM_compute,
        compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
QED

Theorem registered_case10173_historical_sqrt_hessian_decimal_lengths:
  !indices hessian result.
    bounded_historical_sqrt_hessian_decimal derivative logarithmic_derivative
      gradient indices hessian = SOME result ==>
    LENGTH hessian = LENGTH indices /\ LENGTH result = LENGTH indices
Proof
  Induct_on `indices`
  >- (Cases_on `hessian`
      >> simp
           [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_hessian_decimal_def])
  >> Cases_on `h`
  >> Cases_on `hessian`
  >> rw
       [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_hessian_decimal_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_historical_b_hessian_decimal_length:
  bounded_historical_b_hessian_decimal root_delta two_over_root_four
      diagonal_reciprocal root_gradient base_hessian = SOME result ==>
  LENGTH result = 21
Proof
  rw
    [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_b_hessian_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_historical_second_hessian_decimal_lengths:
  !indices delta_hessian b_hessian result.
    bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      indices delta_hessian b_hessian = SOME result ==>
    LENGTH delta_hessian = LENGTH indices /\
    LENGTH b_hessian = LENGTH indices /\
    LENGTH result = LENGTH indices
Proof
  Induct_on `indices`
  >- (Cases_on `delta_hessian`
      >> Cases_on `b_hessian`
      >> simp
           [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_decimal_def])
  >> Cases_on `h`
  >> Cases_on `delta_hessian`
  >> Cases_on `b_hessian`
  >> rw
       [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_decimal_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

val _ = export_theory ();
