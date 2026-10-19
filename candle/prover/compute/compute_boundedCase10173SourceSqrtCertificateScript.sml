(*****************************************************************************
 * Exact source-rational square-root certificate boundary for case 10173.
 *
 * The fast decimal checker validates rounded roots.  Source refinement also
 * needs the unchanged rational checker inequalities before rounding.  This
 * first-order predicate checks those exact cross-products directly on the
 * authenticated source cvals; it is suitable for compiled batch execution.
 *****************************************************************************)
Theory compute_boundedCase10173SourceSqrtCertificate
Ancestors
  compute_registeredCase10173RootInputsBinding
Libs
  bossLib preamble intLib

Definition bounded_case10173_source_q_sqrt_certificate_exact_def:
  bounded_case10173_source_q_sqrt_certificate_exact input output <=>
    case bounded_object_q_interval_ints input of
    | NONE => F
    | SOME ((input_lower,input_lower_denominator),
            (input_upper,input_upper_denominator)) =>
      case bounded_object_q_interval_ints output of
      | NONE => F
      | SOME ((output_lower,output_lower_denominator),
              (output_upper,output_upper_denominator)) =>
        0 < input_lower /\
        0 < output_lower /\
        input_lower * input_upper_denominator <=
          input_upper * input_lower_denominator /\
        output_lower * output_upper_denominator <=
          output_upper * output_lower_denominator /\
        output_lower * output_lower * input_lower_denominator <=
          input_lower * output_lower_denominator *
            output_lower_denominator /\
        input_upper * output_upper_denominator *
            output_upper_denominator <=
          output_upper * output_upper * input_upper_denominator
End

Definition bounded_case10173_source_q_sqrt_prefix_exact_def:
  bounded_case10173_source_q_sqrt_prefix_exact 0 inputs roots = T /\
  bounded_case10173_source_q_sqrt_prefix_exact (SUC remaining)
      (Pair input inputs) (Pair root roots) =
    (bounded_case10173_source_q_sqrt_certificate_exact input root /\
     bounded_case10173_source_q_sqrt_prefix_exact remaining inputs roots) /\
  bounded_case10173_source_q_sqrt_prefix_exact (SUC remaining) _ _ = F
End

Definition bounded_case10173_source_coordinate_sqrts_exact_def:
  bounded_case10173_source_coordinate_sqrts_exact
      (Pair box_sqrt_data (Pair center_sqrt_data source_boxes) : cv) =
    (case registered_case10173_q_center_environment_positive source_boxes of
     | NONE => F
     | SOME center_boxes =>
         bounded_case10173_source_q_sqrt_prefix_exact 6
           center_boxes center_sqrt_data /\
         bounded_case10173_source_q_sqrt_prefix_exact 6
           source_boxes box_sqrt_data) /\
  bounded_case10173_source_coordinate_sqrts_exact _ = F
End

Theorem bounded_case10173_source_coordinate_sqrts_exact_components:
  bounded_case10173_source_coordinate_sqrts_exact object_job ==>
  ?box_sqrt_data center_sqrt_data source_boxes center_boxes.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    registered_case10173_q_center_environment_positive source_boxes =
      SOME center_boxes /\
    bounded_case10173_source_q_sqrt_prefix_exact 6
      center_boxes center_sqrt_data /\
    bounded_case10173_source_q_sqrt_prefix_exact 6
      source_boxes box_sqrt_data
Proof
  Cases_on `object_job`
  >> rw [bounded_case10173_source_coordinate_sqrts_exact_def]
  >> Cases_on `c0`
  >> gvs [bounded_case10173_source_coordinate_sqrts_exact_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case10173_source_q_sqrt_prefix_exact_cons:
  bounded_case10173_source_q_sqrt_prefix_exact (SUC remaining)
      (Pair input inputs) (Pair root roots) ==>
  bounded_case10173_source_q_sqrt_certificate_exact input root /\
  bounded_case10173_source_q_sqrt_prefix_exact remaining inputs roots
Proof
  simp [bounded_case10173_source_q_sqrt_prefix_exact_def]
QED

val _ = export_theory ();
