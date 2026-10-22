(*****************************************************************************
 * Authenticated source contract for the generic historical item evaluator.
 *
 * This theorem packages the independently checked job, center, source-radius,
 * and root-record bindings into the exact arguments consumed by the reusable
 * packet-parametric historical item evaluation theorem.  It is deliberately
 * quantified over an arbitrary authenticated packet: no closed fixture or
 * packet-specific evaluator replay is used here.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalItemAuthenticatedEval
Ancestors
  compute_registeredCase10173HistoricalItemGeneralEval
  compute_registeredCase10173HistProgramMemoEval
Libs
  bossLib preamble

Theorem registered_case10173_authenticated_packet_hist_item_eval_above:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_box_binds_object_job
    packet object_job /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record /\
  bounded_case10173_decimal_packet_source_radii_exact
    packet object_job ==>
  ?box_sqrt_data center_sqrt_data source_boxes center_boxes result.
    object_job =
      Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    registered_case10173_q_center_environment_positive source_boxes =
      SOME center_boxes /\
    bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME (bounded_case10173_packet_center_environment packet) /\
    bounded_object_positive_q_interval64_decimal_list source_boxes =
      SOME (bounded_case10173_packet_box_environment packet) /\
    bounded_case10173_source_radii64_positive_q source_boxes =
      SOME (bounded_case10173_packet_radii packet) /\
    bounded_interval64_object_cv_list
      (bounded_case10173_packet_root_intervals packet) = root_record /\
    registered_case10173_hist_item_eval_above 30000
      center_boxes source_boxes
      (registered_case10173_q_cv_list
        (MAP
          (\value.
            (bounded_word64_object_cv value,Num 999999999999))
          (bounded_case10173_packet_radii packet)))
      root_record (Pair (Num 1) result)
Proof
  strip_tac
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_components
  >> imp_res_tac
       compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_center_exact_components
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_root_binding_exact_cv
  >> imp_res_tac
       compute_registeredCase10173RadiusBindingTheory.bounded_case10173_decimal_packet_source_radii_exact_components
  >> gvs
       [compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def]
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_item_eval_above_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_as_signed64]
         compute_registeredCase10173HistoricalItemGeneralEvalTheory.registered_case10173_historical_item_packet_accessor_eval)
  >> simp []
QED

val _ = export_theory ();
