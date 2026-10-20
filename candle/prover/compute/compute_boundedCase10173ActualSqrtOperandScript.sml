(*****************************************************************************
 * Authenticated square-root contract on the actual Taylor operand.
 *
 * The unchanged source evaluator first Taylor-completes each coordinate
 * variable and passes that result's value_bound to sqrt.  The original source
 * box is therefore not the literal sqrt operand.  This theory recomputes the
 * completed variable from packet radii and centers, converts its value bound
 * to the positive rational representation used by the generic source bridge,
 * and authenticates both the source domain certificate and the direct
 * second-derivative rounding on that value.
 *****************************************************************************)
Theory compute_boundedCase10173ActualSqrtOperand
Ancestors
  compute_boundedCase10173SourceDecimalExact
  compute_boundedCase10173SourceSqrtCertificate
  compute_boundedCase10173HistoricalCellDecimal
Libs
  bossLib preamble

Definition bounded_case10173_actual_variable_decimal_def:
  bounded_case10173_actual_variable_decimal radii center_environment index =
    if LENGTH radii <> 6 \/ LENGTH center_environment <> 6
    then NONE
    else
      case bounded_interval64_unit_vector_decimal index of
      | NONE => NONE
      | SOME gradient =>
        case bounded_interval64_nth center_environment index of
        | NONE => NONE
        | SOME center_value =>
            bounded_taylor64_complete_decimal radii T center_value gradient
              (bounded_interval64_zeros 21)
End

Definition bounded_case10173_positive_interval64_q_cv_def:
  bounded_case10173_positive_interval64_q_cv
      (BoundedInterval64
        (BoundedSigned64 lower_negative lower_magnitude)
        (BoundedSigned64 upper_negative upper_magnitude)) =
    if lower_negative \/ upper_negative then NONE
    else
      SOME
        (Pair
          (bounded_case10173_positive_endpoint64_q_cv
            (BoundedSigned64 F lower_magnitude))
          (bounded_case10173_positive_endpoint64_q_cv
            (BoundedSigned64 F upper_magnitude)))
End

Definition bounded_case10173_actual_sqrt_operand_prefix_exact_def:
  bounded_case10173_actual_sqrt_operand_prefix_exact
      0 index radii center_environment box_roots certificates = T /\
  bounded_case10173_actual_sqrt_operand_prefix_exact
      (SUC remaining) index radii center_environment
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) =
    (case bounded_case10173_actual_variable_decimal
       radii center_environment index of
     | NONE => F
     | SOME
         (BoundedTaylor64 domain_flag center_value center_gradient value_bound
           gradient_bounds hessian) =>
       case bounded_case10173_positive_interval64_q_cv value_bound of
       | NONE => F
       | SOME input =>
           domain_flag /\
           bounded_case10173_source_q_sqrt_certificate_exact input box_root /\
           bounded_case10173_source_sqrt_dd_interval64_exact
             box_root input box_second_reciprocal /\
           bounded_case10173_actual_sqrt_operand_prefix_exact
             remaining (SUC index) radii center_environment
             box_roots certificates) /\
  bounded_case10173_actual_sqrt_operand_prefix_exact
      (SUC remaining) index radii center_environment _ _ = F
End

Definition bounded_case10173_source_actual_sqrt_operands_exact_def:
  bounded_case10173_source_actual_sqrt_operands_exact
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals)
      (Pair box_sqrt_data (Pair center_sqrt_data source_boxes) : cv) =
    bounded_case10173_actual_sqrt_operand_prefix_exact 6 0 radii
      center_environment box_sqrt_data coordinate_sqrt_certificates /\
  bounded_case10173_source_actual_sqrt_operands_exact _ _ = F
End

Theorem bounded_case10173_actual_variable_decimal_some:
  bounded_case10173_actual_variable_decimal
      radii center_environment index = SOME result ==>
  bounded_taylor64_well_formed result
Proof
  rw [bounded_case10173_actual_variable_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some
QED

Theorem bounded_case10173_actual_sqrt_operand_prefix_exact_cons:
  bounded_case10173_actual_sqrt_operand_prefix_exact
      (SUC remaining) index radii center_environment
      (Pair box_root box_roots)
      (BoundedCase10173Sqrt64Certificate center_sqrt box_sqrt
        center_derivative box_derivative box_second_reciprocal::certificates) ==>
  ?domain_flag center_value center_gradient value_bound gradient_bounds hessian input.
    bounded_case10173_actual_variable_decimal
      radii center_environment index =
        SOME
          (BoundedTaylor64 domain_flag center_value center_gradient value_bound
            gradient_bounds hessian) /\
    bounded_case10173_positive_interval64_q_cv value_bound = SOME input /\
    domain_flag /\
    bounded_case10173_source_q_sqrt_certificate_exact input box_root /\
    bounded_case10173_source_sqrt_dd_interval64_exact
      box_root input box_second_reciprocal /\
    bounded_case10173_actual_sqrt_operand_prefix_exact
      remaining (SUC index) radii center_environment box_roots certificates
Proof
  simp [bounded_case10173_actual_sqrt_operand_prefix_exact_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case10173_source_actual_sqrt_operands_exact_components:
  bounded_case10173_source_actual_sqrt_operands_exact packet object_job ==>
  ?radii center_environment box_environment coordinate_sqrt_certificates
   center_root_delta center_root_four_x0 center_reciprocals box_root_delta
   box_root_four_x0 box_reciprocals box_sqrt_data center_sqrt_data source_boxes.
    packet =
      BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals /\
    object_job = Pair box_sqrt_data (Pair center_sqrt_data source_boxes) /\
    bounded_case10173_actual_sqrt_operand_prefix_exact 6 0 radii
      center_environment box_sqrt_data coordinate_sqrt_certificates
Proof
  Cases_on `packet`
  >> Cases_on `object_job`
  >> rw [bounded_case10173_source_actual_sqrt_operands_exact_def]
  >> Cases_on `c0`
  >> gvs [bounded_case10173_source_actual_sqrt_operands_exact_def]
QED

val _ = export_theory ();
