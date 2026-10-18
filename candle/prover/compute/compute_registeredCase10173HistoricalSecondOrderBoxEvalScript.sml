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

Theorem registered_case10173_historical_box_u126_typed_eval:
  bounded_historical_u126_decimal
      registered_case10173_historical_box_environment_decimal =
    SOME (value,gradient) /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv registered_case10173_historical_box_environment_object])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv value)
          (bounded_interval64_object_cv_list gradient))),refs)
Proof
  rpt strip_tac
  >> mp_tac registered_case10173_historical_box_u126_exact_eval
  >> impl_tac >- simp []
  >> strip_tac
  >> gvs []
QED

Theorem registered_case10173_historical_box_u135_typed_eval:
  bounded_historical_u135_decimal
      registered_case10173_historical_box_environment_decimal =
    SOME (value,gradient) /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv registered_case10173_historical_box_environment_object])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv value)
          (bounded_interval64_object_cv_list gradient))),refs)
Proof
  rpt strip_tac
  >> mp_tac registered_case10173_historical_box_u135_exact_eval
  >> impl_tac >- simp []
  >> strip_tac
  >> gvs []
QED

Theorem registered_case10173_historical_two_over_root_four_general_typed_eval:
  bounded_historical_scale2 bounded_atan_one_decimal = SOME two /\
  bounded_interval64_positive_inv_certificate_decimal root_four reciprocal /\
  bounded_interval64_mul_decimal two reciprocal = SOME result /\
  140 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_angle_interval_scale»
          [Num 2;App «candle_cv_fs_interval_one» []];
         App «candle_cv_fs_hist_positive_inv»
          [from_cv (bounded_interval64_object_cv root_four)]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv two`
  >> qexists_tac `bounded_interval64_object_cv reciprocal`
  >> conj_tac
  >- (irule
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
      >> first_assum ACCEPT_TAC)
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_atan_one_scale2_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_special_gradient_general_typed_eval:
  bounded_historical_scale2 root_delta = SOME twice_root_delta /\
  bounded_interval64_positive_inv_certificate_decimal
    twice_root_delta reciprocal /\
  bounded_interval64_mul_decimal root_four reciprocal = SOME result /\
  140 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv (bounded_interval64_object_cv root_four);
         App «candle_cv_fs_hist_positive_inv»
          [App «candle_cv_fs_angle_interval_scale»
            [Num 2;from_cv (bounded_interval64_object_cv root_delta)]]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv root_four`
  >> qexists_tac `bounded_interval64_object_cv reciprocal`
  >> conj_tac
  >- (irule
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
      >> first_assum ACCEPT_TAC)
  >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
  >> irule
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_positive_inv_after_scale2_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `twice_root_delta`
  >> simp
       [compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_interval_scale_two_object_typed_exact]
QED

Theorem registered_case10173_historical_reciprocal_u_general_typed_eval:
  bounded_interval64_mul_decimal u126 u135 = SOME u_product /\
  bounded_interval64_positive_inv_certificate_decimal u_product reciprocal /\
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
                 (bounded_interval64_object_cv_list u135_gradient)))]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv reciprocal)),refs)
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
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_object_cv u126`
      >> qexists_tac `bounded_interval64_object_cv u135`
      >> conj_tac
      >- (irule
            compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
          >> first_assum ACCEPT_TAC)
      >> simp
           [compute_execTheory.from_cv_def,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_positive_inv_pair_fst_typed_eval:
  bounded_interval64_positive_inv_certificate_decimal value reciprocal /\
  40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_positive_inv»
        [Uop Fst
          (from_cv
            (Pair (bounded_interval64_object_cv value)
              (bounded_interval64_object_cv_list gradient)))]) refs =
    (M_success (from_cv (bounded_interval64_object_cv reciprocal)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_positive_inv»
            [from_cv (bounded_interval64_object_cv value)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> simp
           [compute_execTheory.from_cv_def,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
  >> irule
       compute_registeredCase10173HistoricalInverseEvalTheory.registered_case10173_fs_hist_positive_inv_certificate_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_log_u_gradient_pairs_typed_eval:
  LENGTH u126_gradient = 6 /\
  LENGTH u135_gradient = 6 /\
  registered_case10173_log_u_gradient_decimal u126_gradient reciprocal_u126
    u135_gradient reciprocal_u135 = SOME result /\
  40 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_log_u_gradient»
        [Uop Snd
          (from_cv
            (Pair (bounded_interval64_object_cv u126)
              (bounded_interval64_object_cv_list u126_gradient)));
         from_cv (bounded_interval64_object_cv reciprocal_u126);
         Uop Snd
          (from_cv
            (Pair (bounded_interval64_object_cv u135)
              (bounded_interval64_object_cv_list u135_gradient)));
         from_cv (bounded_interval64_object_cv reciprocal_u135)]) refs =
    (M_success
      (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_log_u_gradient»
            [from_cv (bounded_interval64_object_cv_list u126_gradient);
             from_cv (bounded_interval64_object_cv reciprocal_u126);
             from_cv (bounded_interval64_object_cv_list u135_gradient);
             from_cv (bounded_interval64_object_cv reciprocal_u135)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> simp
           [compute_execTheory.from_cv_def,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
            compute_execProofTheory.compute_eval_from_cv])
  >> irule
       compute_registeredCase10173HistoricalLogUGradientEvalTheory.registered_case10173_fs_hist_log_u_gradient_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_u126_decimal_gradient_length:
  bounded_historical_u126_decimal environment = SOME (value,gradient) ==>
  LENGTH environment = 6 /\ LENGTH gradient = 6
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u126_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_historical_u135_decimal_gradient_length:
  bounded_historical_u135_decimal environment = SOME (value,gradient) ==>
  LENGTH environment = 6 /\ LENGTH gradient = 6
Proof
  rw
    [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u135_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_bounded_hessian64_rows_success_length:
  bounded_hessian64_rows hessian = SOME rows ==>
  LENGTH hessian = 21 /\ LENGTH rows = 6 /\
  EVERY (\row. LENGTH row = 6) rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
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

Theorem registered_case10173_historical_scale2_result_unique:
  bounded_historical_scale2 input = SOME left /\
  bounded_historical_scale2 input = SOME right ==>
  left = right
Proof
  strip_tac
  >> gvs []
QED

Theorem registered_case10173_historical_box_second_order_typed_eval:
  bounded_historical_dihedral_second64_decimal
      registered_case10173_historical_box_environment_decimal
      registered_case10173_historical_box_root_delta
      registered_case10173_historical_box_root_four_x0
      registered_case10173_historical_box_reciprocals =
    SOME (value,gradient,hessian) /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  1000 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv registered_case10173_historical_box_environment_object;
         from_cv
           (bounded_interval64_object_cv
             registered_case10173_historical_box_root_delta);
         from_cv
           (bounded_interval64_object_cv
             registered_case10173_historical_box_root_four_x0)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv value)
          (Pair (bounded_interval64_object_cv_list gradient)
            (bounded_interval64_object_cv_matrix hessian_rows)))),refs)
Proof
  rpt strip_tac
  >> qpat_x_assum
       `bounded_historical_dihedral_second64_decimal _ _ _
          registered_case10173_historical_box_reciprocals = _`
       mp_tac
  >> simp [registered_case10173_historical_box_reciprocals_components]
  >> strip_tac
  >> qpat_x_assum
       `SOME (value,gradient,hessian) =
        bounded_historical_dihedral_second64_decimal _ _ _ _`
       (fn th => assume_tac (GSYM th))
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_second_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_sqrt_second_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_x4_second_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       registered_case10173_bounded_hessian64_rows_success_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaSecondEvalTheory.registered_case10173_bounded_historical_delta_gradient_box_decimal_shape
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_scale_decimal_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_delta_x4_gradient_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_add_at_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_c_vector_decimal_lengths
  >> imp_res_tac
       compute_boundedIntervalListTheory.bounded_interval64_list_add_length
  >> imp_res_tac
       compute_boundedHistoricalDihedralSecondTheory.bounded_historical_replace_three_length
  >> imp_res_tac registered_case10173_historical_u126_decimal_gradient_length
  >> imp_res_tac registered_case10173_historical_u135_decimal_gradient_length
  >> imp_res_tac
       compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_x4_hessian_decimal_length
  >> imp_res_tac registered_case10173_historical_sqrt_hessian_decimal_lengths
  >> imp_res_tac registered_case10173_historical_b_hessian_decimal_length
  >> imp_res_tac registered_case10173_historical_second_hessian_decimal_lengths
  >> `LENGTH bounded_delta64_hessian_indices = 21` by EVAL_TAC
  >> `?root_hessian_rows.
        bounded_hessian64_rows root_hessian = SOME root_hessian_rows /\
        LENGTH root_hessian_rows = 6 /\
        EVERY (\row. LENGTH row = 6) root_hessian_rows` by
       metis_tac [registered_case10173_bounded_hessian64_rows_from_length]
  >> `?delta_x4_hessian_rows.
        bounded_hessian64_rows delta_x4_hessian =
          SOME delta_x4_hessian_rows /\
        LENGTH delta_x4_hessian_rows = 6 /\
        EVERY (\row. LENGTH row = 6) delta_x4_hessian_rows` by
       metis_tac [registered_case10173_bounded_hessian64_rows_from_length]
  >> `?b_hessian_base_rows.
        bounded_hessian64_rows b_hessian_base =
          SOME b_hessian_base_rows /\
        LENGTH b_hessian_base_rows = 6 /\
        EVERY (\row. LENGTH row = 6) b_hessian_base_rows` by
       metis_tac [registered_case10173_bounded_hessian64_rows_from_length]
  >> `?b_hessian_rows.
        bounded_hessian64_rows b_hessian = SOME b_hessian_rows /\
        LENGTH b_hessian_rows = 6 /\
        EVERY (\row. LENGTH row = 6) b_hessian_rows` by
       metis_tac [registered_case10173_bounded_hessian64_rows_from_length]
  >> `bounded_interval64_matrix_scale_decimal
        registered_case10173_historical_box_root_four_x0
        root_hessian_rows = SOME b_hessian_base_rows` by
       metis_tac
         [compute_boundedObjectTaylorStateDecimalTheory.bounded_hessian64_rows_scale_decimal]
  >> `registered_case10173_b_hessian_rows_decimal
        registered_case10173_historical_box_root_delta
        two_over_root_four
        registered_case10173_historical_box_diagonal_reciprocal
        root_gradient b_hessian_base_rows = SOME b_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalBHessianEvalTheory.registered_case10173_b_hessian_rows_decimal_compact]
  >> `registered_case10173_log_u_gradient_decimal u126_gradient
        registered_case10173_historical_box_u126_reciprocal
        u135_gradient
        registered_case10173_historical_box_u135_reciprocal =
      SOME logarithmic_u_gradient` by
       metis_tac
         [compute_registeredCase10173HistoricalLogUGradientEvalTheory.registered_case10173_log_u_gradient_decimal_compact]
  >> `registered_case10173_final_hessian_rows_decimal delta_x4 b
        registered_case10173_historical_box_u_reciprocal
        delta_x4_gradient delta_x4_hessian_rows b_gradient b_hessian_rows
        gradient logarithmic_u_gradient = SOME hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalFinalHessianEvalTheory.registered_case10173_final_hessian_rows_decimal_compact]
  >> `LENGTH registered_case10173_historical_box_environment_decimal = 6 /\
      LENGTH u126_gradient = 6` by
       simp []
  >> `bounded_interval64_nth
        registered_case10173_historical_box_environment_decimal 0 =
      SOME
        (EL 0 registered_case10173_historical_box_environment_decimal)` by
       (irule
          compute_registeredCase10173HistoricalFinalHessianEvalTheory.registered_case10173_bounded_interval64_nth_el
        >> simp [])
  >> `x0 = EL 0 registered_case10173_historical_box_environment_decimal` by
       (qpat_x_assum
          `bounded_interval64_nth
             registered_case10173_historical_box_environment_decimal 0 =
           SOME x0`
          mp_tac
        >> qpat_x_assum
             `bounded_interval64_nth
                registered_case10173_historical_box_environment_decimal 0 =
              SOME
                (EL 0
                  registered_case10173_historical_box_environment_decimal)`
             mp_tac
        >> simp [])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderEvalTheory.registered_case10173_fs_hist_second_order_composition_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv b`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient_base`
  >> qexists_tac `bounded_interval64_object_cv_matrix b_hessian_rows`
  >> qexists_tac `bounded_interval64_object_cv_list c`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv delta_interval)
          (Pair (bounded_interval64_object_cv_list delta_gradient)
            (bounded_interval64_object_cv_matrix derivative_rows))`
  >> qexists_tac `bounded_interval64_object_cv_list delta_x4_gradient`
  >> qexists_tac `bounded_interval64_object_cv_matrix delta_x4_hessian_rows`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv delta_x4)
          (Pair (bounded_interval64_object_cv_list delta_x4_gradient)
            (bounded_interval64_object_cv_matrix delta_x4_hessian_rows))`
  >> qexists_tac `bounded_interval64_object_cv delta_x4`
  >> qexists_tac `bounded_interval64_object_cv_list gradient_base`
  >> qexists_tac `bounded_interval64_object_cv_list logarithmic_u_gradient`
  >> qexists_tac `bounded_interval64_object_cv quotient`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_box_u_reciprocal`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_box_u126_reciprocal`
  >> qexists_tac
       `bounded_interval64_object_cv
          registered_case10173_historical_box_u135_reciprocal`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv root_value)
          (Pair (bounded_interval64_object_cv_list root_gradient)
            (bounded_interval64_object_cv_matrix root_hessian_rows))`
  >> qexists_tac `bounded_interval64_object_cv_list root_gradient`
  >> qexists_tac `bounded_interval64_object_cv_matrix root_hessian_rows`
  >> qexists_tac `bounded_interval64_object_cv special_gradient`
  >> qexists_tac `bounded_interval64_object_cv two_over_root_four`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u126)
          (bounded_interval64_object_cv_list u126_gradient)`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u135)
          (bounded_interval64_object_cv_list u135_gradient)`
  >> qexists_tac `bounded_interval64_object_cv x0`
  >> rpt conj_tac
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_final_value_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_positive_inv_pair_fst_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_box_u126_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (qpat_x_assum
           `x0 =
            EL 0 registered_case10173_historical_box_environment_decimal`
           (fn th => once_rewrite_tac [th])
      >> once_rewrite_tac
        [registered_case10173_historical_box_environment_object_exact]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >- (once_rewrite_tac
        [registered_case10173_historical_box_environment_object_exact]
      >> irule
           compute_registeredCase10173HistoricalDeltaSecondEvalTheory.registered_case10173_fs_hist_delta_second_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_gradient_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_fs_hist_second_sqrt_supplied_typed_eval
      >> simp []
      >> qexists_tac
           `registered_case10173_historical_box_root_derivative`
      >> qexists_tac `delta_hessian`
      >> qexists_tac
           `registered_case10173_historical_box_root_logarithmic`
      >> qexists_tac `root_hessian`
      >> simp []
      >> metis_tac [])
  >- (irule
        compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_hist_replace_three_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_gradient_eval
      >> intLib.ARITH_TAC)
  >- (once_rewrite_tac
        [registered_case10173_historical_box_environment_object_exact]
      >> irule
           compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_delta_x4_second_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_c_vector_six_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFinalHessianEvalTheory.registered_case10173_fs_hist_final_hessian_rows_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalBHessianEvalTheory.registered_case10173_fs_hist_b_hessian_typed_eval
      >> simp []
      >> conj_tac
      >- (`?r0 r1 r2 r3 r4 r5.
             root_hessian_rows = [r0;r1;r2;r3;r4;r5]` by
            metis_tac
              [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases]
          >> gvs []
          >> intLib.ARITH_TAC)
      >> qexists_tac
           `registered_case10173_historical_box_diagonal_reciprocal`
      >> simp [])
  >- (irule registered_case10173_historical_log_u_gradient_pairs_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_two_over_root_four_general_typed_eval
      >> simp []
      >> qexists_tac
           `registered_case10173_historical_box_root_four_reciprocal`
      >> simp [])
  >- (irule registered_case10173_historical_reciprocal_u_general_typed_eval
      >> simp []
      >> qexists_tac `u_product`
      >> simp [])
  >- (irule
        compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_fs_hist_second_value_eval
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_box_u135_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_historical_positive_inv_pair_fst_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_quotient_typed_eval
      >> qexists_tac
           `registered_case10173_historical_box_b_reciprocal`
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_b_gradient_six_typed_eval
      >> qexists_tac `b_correction`
      >> rpt conj_tac
      >- simp []
      >- simp []
      >- (irule
            compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> irule
       (Q.INST
         [`twice_root_delta` |-> `twice_root_delta`,
          `reciprocal` |->
            `registered_case10173_historical_box_special_root_reciprocal`]
         registered_case10173_historical_special_gradient_general_typed_eval)
  >> simp []
  >> metis_tac [registered_case10173_historical_scale2_result_unique]
QED

val _ = export_theory ();
