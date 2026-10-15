(*****************************************************************************
 * Direct semantic boundary for an accepted specialized case-10173 packet.
 *
 * This theory does not try to reproduce the historical object's independently
 * rounded auxiliary-root bytes.  Instead it exposes the facts actually
 * checked by the fast implementation: both historical dihedral calls
 * succeeded, and all four supplied roots are certified against radicands
 * recomputed from the packet's center/box environments.  Coupled with the
 * exact rational source-box relation, this is the appropriate input to the
 * reusable analytic soundness bridge.
 *****************************************************************************)
Theory compute_boundedCase10173SemanticBoundary
Ancestors
  compute_boundedCase10173JobBinding
Libs
  bossLib preamble

Theorem bounded_case10173_packet_accepts_dihedral_calls:
  bounded_case10173_packet_accepts
    (BoundedCase10173Packet radii center_environment box_environment
      coordinate_sqrt_certificates center_root_delta center_root_four_x0
      center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) ==>
  ?center_result box_result.
    bounded_historical_dihedral_first64 center_environment
      center_root_delta center_root_four_x0 center_reciprocals =
        SOME center_result /\
    bounded_historical_dihedral_second64 box_environment
      box_root_delta box_root_four_x0 box_reciprocals =
        SOME box_result
Proof
  rw [compute_boundedCase10173PacketTheory.bounded_case10173_packet_accepts_def,
      compute_boundedCase10173HistoricalCellTheory.bounded_case10173_checked_cell_accepts_def]
  >> Cases_on
       `bounded_case10173_checked_cell64 radii center_environment
          box_environment coordinate_sqrt_certificates center_root_delta
          center_root_four_x0 center_reciprocals box_root_delta
          box_root_four_x0 box_reciprocals`
  >> gvs []
  >> fs [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_checked_cell64_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_historical_dihedral_first64_root_certificates:
  bounded_historical_dihedral_first64 environment root_delta root_four_x0
      reciprocal_certificates = SOME result ==>
  ?delta x0 four_x0.
    bounded_delta64_value environment = SOME delta /\
    bounded_interval64_sqrt_certificate delta root_delta /\
    bounded_interval64_nth environment 0 = SOME x0 /\
    bounded_interval64_scale4 x0 = SOME four_x0 /\
    bounded_interval64_sqrt_certificate four_x0 root_four_x0
Proof
  simp [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_dihedral_first64_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> metis_tac []
QED

Theorem bounded_historical_dihedral_second64_root_certificates:
  bounded_historical_dihedral_second64 environment root_delta root_four_x0
      reciprocal_certificates = SOME result ==>
  ?delta delta_gradient delta_hessian x0 four_x0.
    bounded_historical_delta_second environment =
      SOME (delta,delta_gradient,delta_hessian) /\
    bounded_interval64_sqrt_certificate delta root_delta /\
    bounded_interval64_nth environment 0 = SOME x0 /\
    bounded_interval64_scale4 x0 = SOME four_x0 /\
    bounded_interval64_sqrt_certificate four_x0 root_four_x0
Proof
  simp [compute_boundedHistoricalDihedralSecondTheory.bounded_historical_dihedral_second64_def,
        compute_boundedHistoricalDihedralSecondTheory.bounded_historical_sqrt_second_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> metis_tac []
QED

Definition bounded_case10173_packet_historical_root_contract_def:
  bounded_case10173_packet_historical_root_contract
    (BoundedCase10173Packet radii center_environment box_environment
      coordinate_sqrt_certificates center_root_delta center_root_four_x0
      center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
  ?center_result center_delta center_x0 center_four_x0
   box_result box_delta box_delta_gradient
   box_delta_hessian box_x0 box_four_x0.
    bounded_historical_dihedral_first64 center_environment
      center_root_delta center_root_four_x0 center_reciprocals =
        SOME center_result /\
    bounded_delta64_value center_environment = SOME center_delta /\
    bounded_interval64_sqrt_certificate center_delta center_root_delta /\
    bounded_interval64_nth center_environment 0 = SOME center_x0 /\
    bounded_interval64_scale4 center_x0 = SOME center_four_x0 /\
    bounded_interval64_sqrt_certificate
      center_four_x0 center_root_four_x0 /\
    bounded_historical_dihedral_second64 box_environment
      box_root_delta box_root_four_x0 box_reciprocals = SOME box_result /\
    bounded_historical_delta_second box_environment =
      SOME (box_delta,box_delta_gradient,box_delta_hessian) /\
    bounded_interval64_sqrt_certificate box_delta box_root_delta /\
    bounded_interval64_nth box_environment 0 = SOME box_x0 /\
    bounded_interval64_scale4 box_x0 = SOME box_four_x0 /\
    bounded_interval64_sqrt_certificate box_four_x0 box_root_four_x0
End

Theorem bounded_case10173_packet_accepts_historical_root_contract:
  bounded_case10173_packet_accepts
    (BoundedCase10173Packet radii center_environment box_environment
      coordinate_sqrt_certificates center_root_delta center_root_four_x0
      center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) ==>
  ?center_result center_delta center_x0 center_four_x0
   box_result box_delta box_delta_gradient
   box_delta_hessian box_x0 box_four_x0.
    bounded_historical_dihedral_first64 center_environment
      center_root_delta center_root_four_x0 center_reciprocals =
        SOME center_result /\
    bounded_delta64_value center_environment = SOME center_delta /\
    bounded_interval64_sqrt_certificate center_delta center_root_delta /\
    bounded_interval64_nth center_environment 0 = SOME center_x0 /\
    bounded_interval64_scale4 center_x0 = SOME center_four_x0 /\
    bounded_interval64_sqrt_certificate
      center_four_x0 center_root_four_x0 /\
    bounded_historical_dihedral_second64 box_environment
      box_root_delta box_root_four_x0 box_reciprocals =
        SOME box_result /\
    bounded_historical_delta_second box_environment =
      SOME (box_delta,box_delta_gradient,box_delta_hessian) /\
    bounded_interval64_sqrt_certificate box_delta box_root_delta /\
    bounded_interval64_nth box_environment 0 = SOME box_x0 /\
    bounded_interval64_scale4 box_x0 = SOME box_four_x0 /\
    bounded_interval64_sqrt_certificate box_four_x0 box_root_four_x0
Proof
  strip_tac
  >> drule bounded_case10173_packet_accepts_dihedral_calls
  >> strip_tac
  >> imp_res_tac bounded_historical_dihedral_first64_root_certificates
  >> imp_res_tac bounded_historical_dihedral_second64_root_certificates
  >> metis_tac []
QED

Theorem bounded_case10173_packet_accepts_historical_root_contract_predicate:
  bounded_case10173_packet_accepts packet ==>
  bounded_case10173_packet_historical_root_contract packet
Proof
  Cases_on `packet`
  >> rw [bounded_case10173_packet_historical_root_contract_def]
  >> imp_res_tac bounded_case10173_packet_accepts_historical_root_contract
  >> metis_tac []
QED

Theorem bounded_case10173_packet_object_job_direct_boundary:
  bounded_case10173_packet_accepts packet /\
  bounded_case10173_packet_box_binds_object_job packet object_job ==>
  (?source_boxes.
     bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
     bounded_interval64_list_covers_object_q
       (bounded_case10173_packet_box_environment packet) source_boxes) /\
  bounded_case10173_packet_accepts packet
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_binds_object_job_components
  >> metis_tac []
QED

val _ = export_theory ();
