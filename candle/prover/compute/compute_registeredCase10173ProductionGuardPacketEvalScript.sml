(*****************************************************************************
 * Accepted-packet refinement for the complete historical production guard.
 *
 * The packet checker authenticates every numerical premise consumed here.
 * This layer extracts those premises from the successful source traces and
 * applies the packet-independent twelve-binding evaluator theorem.
 *****************************************************************************)
Theory compute_registeredCase10173ProductionGuardPacketEval
Ancestors
  compute_registeredCase10173ProductionGuardFullEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_mul_decimal_success_valid_inputs:
  bounded_interval64_mul_decimal left right = SOME product ==>
  bounded_interval64_valid left /\ bounded_interval64_valid right
Proof
  simp [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def]
QED

Theorem registered_case10173_positive_inv_certificate_input_facts:
  bounded_interval64_positive_inv_certificate_decimal input output ==>
  bounded_interval64_valid input /\
  bounded_interval64_valid output /\
  bounded_signed64_strict_positive (bounded_interval64_lower input)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp
       [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_def,
        compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def]
QED

Theorem registered_case10173_positive_sqrt_certificate_output_facts:
  bounded_interval64_positive_sqrt_certificate_decimal input output ==>
  bounded_interval64_valid output /\
  bounded_signed64_strict_positive (bounded_interval64_lower output)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp
       [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_def,
        compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def]
QED

Theorem registered_case10173_positive_product_from_mul_inv:
  bounded_signed64_strict_positive (bounded_interval64_lower left) /\
  bounded_signed64_strict_positive (bounded_interval64_lower right) /\
  bounded_interval64_mul_decimal left right = SOME product /\
  bounded_interval64_positive_inv_certificate_decimal product reciprocal ==>
  0 <
    (w2n
       (bounded_signed64_magnitude (bounded_interval64_lower left)) *
     w2n
       (bounded_signed64_magnitude (bounded_interval64_lower right))) DIV
      1000000000000
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173ProductionGuardAuthenticatedEvalTheory.registered_case10173_positive_product_from_decimal_product
  >> imp_res_tac registered_case10173_mul_decimal_success_valid_inputs
  >> imp_res_tac registered_case10173_positive_inv_certificate_input_facts
  >> simp []
QED

Theorem registered_case10173_hist_production_guard_packet_eval:
  bounded_packed_chars_case10173_decimal_packet_ok
      (BoundedCase10173Packet radii
        [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
        coordinate_sqrt_certificates
        center_root_delta center_root_four_x0
        [center_root_derivative;center_root_four_reciprocal;
         center_u_reciprocal;center_special_root_reciprocal;
         center_b_reciprocal]
        box_root_delta box_root_four_x0
        [box_root_derivative;box_root_logarithmic;
         box_root_four_reciprocal;box_diagonal_reciprocal;
         box_u_reciprocal;box_special_root_reciprocal;
         box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) /\
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME [x0;x1;x2;x3;x4;x5] /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME [y0;y1;y2;y3;y4;y5] /\
  36000 +
      8 * (registered_case10173_center_list_length boxes + 1) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv boxes;
         from_cv
           (bounded_interval64_object_cv_list
             [center_root_delta;center_root_four_x0;
              box_root_delta;box_root_four_x0])])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  rpt strip_tac
  >> fs
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def]
  >> every_case_tac
  >> gvs []
  >> drule
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> strip_tac
  >> drule
       compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_sqrt_second_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_x4_second_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_x4_hessian_decimal_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length
  >> imp_res_tac registered_case10173_positive_sqrt_certificate_output_facts
  >> fs
       [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_u_guards_decimal_def]
  >> imp_res_tac registered_case10173_mul_decimal_success_valid_inputs
  >> imp_res_tac
       compute_registeredCase10173ProductionGuardAuthenticatedEvalTheory.registered_case10173_atan_range_none_endpoint_magnitudes
  >> irule registered_case10173_hist_production_guard_typed_eval
  >> simp []
  >> conj_tac
  >- (irule registered_case10173_positive_product_from_mul_inv
      >> simp []
      >> qexists_tac `box_b_reciprocal`
      >> simp [])
  >> conj_tac
  >- (irule registered_case10173_positive_product_from_mul_inv
      >> simp []
      >> qexists_tac `center_b_reciprocal`
      >> simp [])
  >> conj_tac
  >- (qexists_tac `quotient'`
      >> qexists_tac `box_b_reciprocal`
      >> simp []
      >> irule registered_case10173_positive_product_from_mul_inv
      >> simp []
      >> qexists_tac `box_u_reciprocal`
      >> simp [])
  >> qexists_tac `quotient`
  >> qexists_tac `center_b_reciprocal`
  >> simp []
  >> irule registered_case10173_positive_product_from_mul_inv
  >> simp []
  >> qexists_tac `center_u_reciprocal`
  >> simp []
QED

Theorem registered_case10173_hist_production_guard_packet_accessor_eval:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  registered_case10173_q_center_environment_positive boxes =
      SOME center_boxes /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME (bounded_case10173_packet_center_environment packet) /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME (bounded_case10173_packet_box_environment packet) ==>
  !clock refs.
    36000 +
        8 * (registered_case10173_center_list_length boxes + 1) < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_production_guard»
        [from_cv boxes;
         from_cv
           (bounded_interval64_object_cv_list
             (bounded_case10173_packet_root_intervals packet))])
      (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  Cases_on `packet`
  >> simp
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
        compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
        compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def]
  >> rpt strip_tac
  >> fs
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def]
  >> every_case_tac
  >> gvs []
  >> drule
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> strip_tac
  >> drule
       compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173RootRecordAuthenticatedEvalTheory.registered_case10173_root_geometry_ok_lengths
  >> subgoal `LENGTH l0 = 6`
  >- intLib.ARITH_TAC
  >> subgoal `LENGTH l1 = 6`
  >- intLib.ARITH_TAC
  >> qpat_x_assum `LENGTH l0 = LENGTH l` kall_tac
  >> qpat_x_assum `LENGTH l1 = LENGTH l0` kall_tac
  >> qpat_x_assum `LENGTH l1 + 0 = 6` kall_tac
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> irule registered_case10173_hist_production_guard_packet_eval
  >> simp
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def]
  >> metis_tac []
QED

val _ = export_theory ();
