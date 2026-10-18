(*****************************************************************************
 * Exact binding of the historical root-input environments to one genuine
 * case-10173 object job.
 *
 * The box environment already has a canonical decimal binding.  This layer
 * additionally checks that the packet's center environment is precisely the
 * registered rational midpoint construction followed by the registered
 * outward decimal conversion; it is not an independently trusted fixture.
 *****************************************************************************)
Theory compute_registeredCase10173RootInputsBinding
Ancestors
  compute_registeredCase10173CenterEnvironmentObject
  compute_boundedCase10173DecimalInputBinding
Libs
  bossLib preamble wordsLib

Definition bounded_case10173_packet_center_environment_def:
  bounded_case10173_packet_center_environment
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) =
    center_environment
End

Definition bounded_case10173_decimal_packet_center_exact_object_job_def:
  bounded_case10173_decimal_packet_center_exact_object_job packet object_job <=>
    case bounded_case10173_object_job_boxes object_job of
    | NONE => F
    | SOME source_boxes =>
        (case registered_case10173_q_center_environment_positive source_boxes of
         | NONE => F
         | SOME center_boxes =>
             bounded_object_positive_q_interval64_decimal_list center_boxes =
               SOME (bounded_case10173_packet_center_environment packet))
End

Definition bounded_case10173_decimal_packet_root_inputs_exact_def:
  bounded_case10173_decimal_packet_root_inputs_exact packet object_job
      root_record <=>
    bounded_case10173_decimal_packet_exact_input_binding
      packet object_job root_record /\
    bounded_case10173_decimal_packet_center_exact_object_job
      packet object_job
End

Theorem bounded_case10173_decimal_packet_center_exact_components:
  bounded_case10173_decimal_packet_center_exact_object_job packet object_job ==>
  ?source_boxes center_boxes.
    bounded_case10173_object_job_boxes object_job = SOME source_boxes /\
    registered_case10173_q_center_environment_positive source_boxes =
      SOME center_boxes /\
    bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME (bounded_case10173_packet_center_environment packet)
Proof
  rw [bounded_case10173_decimal_packet_center_exact_object_job_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_center_exact_binding:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_center_exact_object_job
      bounded_case10173_decimal_packet0_source_aligned object_job
Proof
  simp
    [compute_boundedCase10173RootBindingTheory.bounded_case10173_checked_call_first_job_root_def,
     bounded_case10173_decimal_packet_center_exact_object_job_def,
     compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def,
     bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_sqrt_certificates_def,
     compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_def,
     compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_midpoint_positive_cv_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
     compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_boundedIntervalTheory.bounded_interval64_valid_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case10173_decimal_packet0_source_aligned_root_inputs_exact:
  ?object_job root_record.
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp =
        SOME (Pair object_job root_record) /\
    bounded_case10173_decimal_packet_root_inputs_exact
      bounded_case10173_decimal_packet0_source_aligned
      object_job root_record
Proof
  qx_choose_then `input_job`
    (qx_choose_then `input_root` strip_assume_tac)
    compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_exact_input_binding
  >> qx_choose_then `center_job`
       (qx_choose_then `center_root` strip_assume_tac)
       bounded_case10173_decimal_packet0_source_aligned_center_exact_binding
  >> `input_job = center_job /\ input_root = center_root` by gvs []
  >> qexists_tac `input_job`
  >> qexists_tac `input_root`
  >> simp [bounded_case10173_decimal_packet_root_inputs_exact_def]
QED

val _ = export_theory ();
