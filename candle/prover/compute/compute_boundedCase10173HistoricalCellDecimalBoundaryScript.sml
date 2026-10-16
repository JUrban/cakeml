(*****************************************************************************
 * Semantic boundary exposed by the complete decimal case-10173 checker.
 *
 * Acceptance exposes the recomputed center/box calls, checked roots, guards,
 * final negative Taylor bound, and the exact rational source box covered by
 * the packet.  No native-capture assertion is used as a theorem premise.
 *****************************************************************************)
Theory compute_boundedCase10173HistoricalCellDecimalBoundary
Ancestors
  compute_boundedCase10173HistoricalCellDecimalData
  compute_boundedCase10173JobBinding
  compute_boundedObjectDecimalQ
Libs
  bossLib preamble wordsLib

Definition bounded_case10173_decimal_packet_accepts_def:
  bounded_case10173_decimal_packet_accepts
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
    bounded_case10173_checked_cell_accepts_decimal radii center_environment
      box_environment coordinate_sqrt_certificates center_root_delta
      center_root_four_x0 center_reciprocals box_root_delta
      box_root_four_x0 box_reciprocals
End

Theorem bounded_case10173_decimal_accepts_guards:
  bounded_case10173_checked_cell_accepts_decimal radii center_environment
      box_environment coordinate_sqrt_certificates center_root_delta
      center_root_four_x0 center_reciprocals box_root_delta
      box_root_four_x0 box_reciprocals ==>
  bounded_case10173_geometry_ok
    box_environment center_environment radii 0 /\
  bounded_case10173_positive_environment center_environment /\
  bounded_case10173_positive_environment box_environment /\
  bounded_case10173_u_guards_decimal center_environment /\
  bounded_case10173_u_guards_decimal box_environment
Proof
  strip_tac
  >> drule
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> strip_tac
  >> fs [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_def]
QED

Theorem bounded_case10173_decimal_accepts_dihedral_calls:
  bounded_case10173_checked_cell_accepts_decimal radii center_environment
      box_environment coordinate_sqrt_certificates center_root_delta
      center_root_four_x0 center_reciprocals box_root_delta
      box_root_four_x0 box_reciprocals ==>
  ?center_result box_result.
    bounded_historical_dihedral_first64_decimal center_environment
      center_root_delta center_root_four_x0 center_reciprocals =
        SOME center_result /\
    bounded_historical_dihedral_second64_decimal box_environment
      box_root_delta box_root_four_x0 box_reciprocals = SOME box_result
Proof
  rw [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_def]
  >> Cases_on
       `bounded_case10173_checked_cell64_decimal radii center_environment
          box_environment coordinate_sqrt_certificates center_root_delta
          center_root_four_x0 center_reciprocals box_root_delta
          box_root_four_x0 box_reciprocals`
  >> gvs []
  >> fs [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_historical_dihedral_first64_decimal_root_certificates:
  bounded_historical_dihedral_first64_decimal environment root_delta
      root_four_x0 reciprocal_certificates = SOME result ==>
  ?delta x0 four_x0.
    bounded_historical_delta64_value_decimal environment = SOME delta /\
    bounded_interval64_sqrt_certificate_decimal delta root_delta /\
    bounded_interval64_nth environment 0 = SOME x0 /\
    bounded_interval64_scale4 x0 = SOME four_x0 /\
    bounded_interval64_sqrt_certificate_decimal four_x0 root_four_x0
Proof
  simp [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> metis_tac []
QED

Theorem bounded_historical_dihedral_second64_decimal_root_certificates:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0 reciprocal_certificates = SOME result ==>
  ?delta delta_gradient delta_hessian x0 four_x0.
    bounded_historical_delta_second_decimal environment =
      SOME (delta,delta_gradient,delta_hessian) /\
    bounded_interval64_sqrt_certificate_decimal delta root_delta /\
    bounded_interval64_nth environment 0 = SOME x0 /\
    bounded_interval64_scale4 x0 = SOME four_x0 /\
    bounded_interval64_sqrt_certificate_decimal four_x0 root_four_x0
Proof
  simp [compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_def,
        compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_second_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> metis_tac []
QED

Definition bounded_case10173_decimal_packet_complete_contract_def:
  bounded_case10173_decimal_packet_complete_contract
    (BoundedCase10173Packet radii center_environment box_environment
      coordinate_sqrt_certificates center_root_delta center_root_four_x0
      center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
  bounded_case10173_geometry_ok
    box_environment center_environment radii 0 /\
  bounded_case10173_positive_environment center_environment /\
  bounded_case10173_positive_environment box_environment /\
  bounded_case10173_u_guards_decimal center_environment /\
  bounded_case10173_u_guards_decimal box_environment /\
  (?center_result box_result.
     bounded_historical_dihedral_first64_decimal center_environment
       center_root_delta center_root_four_x0 center_reciprocals =
         SOME center_result /\
     bounded_historical_dihedral_second64_decimal box_environment
       box_root_delta box_root_four_x0 box_reciprocals = SOME box_result) /\
  (?center_value center_gradient value_bound gradient_bounds hessian.
     bounded_case10173_checked_cell64_decimal radii center_environment
       box_environment coordinate_sqrt_certificates center_root_delta
       center_root_four_x0 center_reciprocals box_root_delta
       box_root_four_x0 box_reciprocals =
         SOME (BoundedTaylor64 T center_value center_gradient value_bound
           gradient_bounds hessian) /\
     bounded_signed64_strict_negative
       (bounded_interval64_upper value_bound))
End

Theorem bounded_case10173_decimal_packet_accepts_complete_contract:
  bounded_case10173_decimal_packet_accepts packet ==>
  bounded_case10173_decimal_packet_complete_contract packet
Proof
  Cases_on `packet`
  >> rw [bounded_case10173_decimal_packet_accepts_def,
         bounded_case10173_decimal_packet_complete_contract_def]
  >> imp_res_tac bounded_case10173_decimal_accepts_guards
  >> imp_res_tac bounded_case10173_decimal_accepts_dihedral_calls
  >> imp_res_tac
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> metis_tac []
QED

Definition bounded_case10173_decimal_packet_box_binds_object_job_def:
  bounded_case10173_decimal_packet_box_binds_object_job packet object_job <=>
    case bounded_case10173_object_job_boxes object_job of
    | NONE => F
    | SOME source_boxes =>
        bounded_interval64_list_covers_object_q_decimal
          (bounded_case10173_packet_box_environment packet) source_boxes
End

Theorem bounded_case10173_decimal_packet_box_binds_object_job_components:
  bounded_case10173_decimal_packet_box_binds_object_job packet object_job ==>
  ?source_boxes.
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q_decimal
      (bounded_case10173_packet_box_environment packet) source_boxes
Proof
  rw [bounded_case10173_decimal_packet_box_binds_object_job_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case10173_decimal_packet0_accepts_predicate:
  bounded_case10173_decimal_packet_accepts
    bounded_case10173_decimal_packet0
Proof
  simp [bounded_case10173_decimal_packet_accepts_def,
        compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
        compute_boundedCase10173PacketTheory.bounded_case10173_packet_case_def]
  >> ACCEPT_TAC
       (SIMP_RULE std_ss
          [compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
           compute_boundedCase10173PacketTheory.bounded_case10173_packet_case_def]
          compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_accepts)
QED

Theorem bounded_case10173_decimal_packet0_complete_contract:
  bounded_case10173_decimal_packet_complete_contract
    bounded_case10173_decimal_packet0
Proof
  match_mp_tac bounded_case10173_decimal_packet_accepts_complete_contract
  >> ACCEPT_TAC bounded_case10173_decimal_packet0_accepts_predicate
QED

Theorem bounded_case10173_decimal_packet0_source_box_binding:
  ?object_job source_boxes.
    bounded_case10173_complete_call_first_job
      registered_case10173_cell0_cexp = SOME object_job /\
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q_decimal
      (bounded_case10173_packet_box_environment
        bounded_case10173_decimal_packet0) source_boxes
Proof
  simp [bounded_case10173_complete_call_first_job_def,
        bounded_case10173_object_job_boxes_def,
        bounded_case10173_packet_box_environment_def,
        compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
        compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_cexp_def,
        compute_pureFastTheory.compute_exp_to_cv_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
  >> simp []
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_decimal_packet0_authenticated_boundary:
  ?object_job source_boxes.
    bounded_case10173_complete_call_first_job
      registered_case10173_cell0_cexp = SOME object_job /\
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    bounded_interval64_list_covers_object_q_decimal
      (bounded_case10173_packet_box_environment
        bounded_case10173_decimal_packet0) source_boxes /\
    bounded_case10173_decimal_packet_complete_contract
      bounded_case10173_decimal_packet0
Proof
  mp_tac bounded_case10173_decimal_packet0_source_box_binding
  >> strip_tac
  >> qexists_tac `object_job`
  >> qexists_tac `source_boxes`
  >> simp [bounded_case10173_decimal_packet0_complete_contract]
QED

val _ = export_theory ();
