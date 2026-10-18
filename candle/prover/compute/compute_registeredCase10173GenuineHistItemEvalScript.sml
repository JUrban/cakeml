(*****************************************************************************
 * Complete registered historical item for the first authenticated genuine
 * case-10173 job.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineHistItemEval
Ancestors
  compute_registeredCase10173GenuineRadiusEval
  compute_registeredCase10173HistoricalFirstOrderCenterEval
  compute_registeredCase10173HistoricalSecondOrderBoxEval
Libs
  bossLib preamble wordsLib

Theorem registered_case10173_first_job_projection:
  SOME
      (Pair
        (Pair box_sqrt_data (Pair center_sqrt_data boxes))
        root_record) =
    bounded_case10173_checked_call_first_job_root
      registered_case10173_historical_chunk16_cexp ==>
  registered_case10173_first_job_boxes = boxes /\
  registered_case10173_first_job_roots = root_record
Proof
  strip_tac
  >> qpat_x_assum `SOME _ = _` (fn th => assume_tac (GSYM th))
  >> simp
    [compute_registeredCase10173RootRecordValueTheory.registered_case10173_first_job_boxes_def,
     compute_registeredCase10173RootRecordValueTheory.registered_case10173_first_job_roots_def]
QED

Theorem registered_case10173_genuine_source_inputs_exact:
  ?center_boxes.
    registered_case10173_q_center_environment_positive
        registered_case10173_first_job_boxes = SOME center_boxes /\
    bounded_object_positive_q_interval64_decimal_list center_boxes =
        SOME registered_case10173_historical_center_environment_decimal /\
    bounded_object_positive_q_interval64_decimal_list
        registered_case10173_first_job_boxes =
        SOME registered_case10173_historical_box_environment_decimal /\
    registered_case10173_first_job_roots =
      bounded_interval64_object_cv_list
        [registered_case10173_historical_center_root_delta;
         registered_case10173_historical_center_root_four_x0;
         registered_case10173_historical_box_root_delta;
         registered_case10173_historical_box_root_four_x0]
Proof
  qx_choose_then `object_job`
    (qx_choose_then `root_record` strip_assume_tac)
    compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet0_source_aligned_root_inputs_exact
  >> qpat_x_assum
       `bounded_case10173_checked_call_first_job_root _ = _`
       (fn th => assume_tac th)
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> drule
       compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_center_exact_components
  >> strip_tac
  >> drule
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_root_binding_exact_cv
  >> strip_tac
  >> Cases_on `object_job`
  >> fs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_object_job_def]
  >> Cases_on `c0`
  >> fs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_object_job_def]
  >> imp_res_tac registered_case10173_first_job_projection
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
        compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
        compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
        compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_root_delta_def,
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_root_four_x0_def,
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_decimal_def,
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_root_delta_def,
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_root_four_x0_def]
  >> metis_tac []
QED

Theorem registered_case10173_genuine_historical_item_complete:
  ?center_value center_gradient box_value box_gradient hessian rows result.
    bounded_historical_dihedral_first64_decimal
      registered_case10173_historical_center_environment_decimal
      registered_case10173_historical_center_root_delta
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_reciprocals =
        SOME (center_value,center_gradient) /\
    bounded_historical_dihedral_second64_decimal
      registered_case10173_historical_box_environment_decimal
      registered_case10173_historical_box_root_delta
      registered_case10173_historical_box_root_four_x0
      registered_case10173_historical_box_reciprocals =
        SOME (box_value,box_gradient,hessian) /\
    bounded_hessian64_rows hessian = SOME rows /\
    bounded_object_fs_taylor_complete
      registered_case10173_historical_radii_words T
      center_value center_gradient hessian rows = SOME result
Proof
  simp
    [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
     compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_root_delta_def,
     compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_root_four_x0_def,
     compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_reciprocals_def,
     compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_decimal_def,
     compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_root_delta_def,
     compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_root_four_x0_def,
     compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_reciprocals_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
  >> EVAL_TAC
  >> gvs []
  >> EVAL_TAC
  >> simp []
  >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
