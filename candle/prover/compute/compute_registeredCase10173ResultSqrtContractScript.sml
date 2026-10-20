(*****************************************************************************
 * Typed source contract for the unchanged square-root result operation.
 *
 * A successful fast decimal square-root calculation already contains all
 * numerical witnesses used by the literal historical source.  This theory
 * first exposes those witnesses and their shape facts, so the registered
 * evaluator theorem does not have to replay any numerical arithmetic.
 *****************************************************************************)
Theory compute_registeredCase10173ResultSqrtContract
Ancestors
  compute_registeredCase10173ActualResultSqrtEval
  compute_boundedObjectTaylorSqrtDecimal
  compute_registeredCase10173HistoricalSecondOrderBoxEval
Libs
  bossLib preamble intLib

Theorem bounded_interval64_valid_strict_positive:
  bounded_interval64_valid interval /\
  bounded_signed64_strict_positive (bounded_interval64_lower interval) ==>
  case interval of
  | BoundedInterval64 lower upper =>
      bounded_signed64_strict_positive lower /\
      bounded_signed64_strict_positive upper
Proof
  Cases_on `interval`
  >> simp [compute_boundedIntervalTheory.bounded_interval64_lower_def]
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct]
  >> strip_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_positive_sqrt_certificate_output_strict:
  bounded_interval64_positive_sqrt_certificate_decimal input output ==>
  case output of
  | BoundedInterval64 lower upper =>
      bounded_signed64_strict_positive lower /\
      bounded_signed64_strict_positive upper
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_sound
  >> imp_res_tac
       compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_nonnegative
  >> match_mp_tac bounded_interval64_valid_strict_positive
  >> fs
       [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def]
QED

Theorem bounded_interval64_positive_inv_certificate_strict:
  bounded_interval64_positive_inv_certificate_decimal input output ==>
  (case input of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper) /\
  (case output of
   | BoundedInterval64 lower upper =>
       bounded_signed64_strict_positive lower /\
       bounded_signed64_strict_positive upper)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> `bounded_interval64_inv_certificate_decimal
        (BoundedInterval64 b b0) (BoundedInterval64 b' b0') /\
      bounded_signed64_strict_positive b` by
       fs
         [compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_def]
  >> imp_res_tac
       compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_positive_signs
  >> fs []
QED

Theorem registered_case10173_taylor_sqrt_decimal_components:
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal source =
    SOME result ==>
  bounded_taylor64_well_formed source /\
  bounded_interval64_positive_sqrt_certificate_decimal
    (case source of
     | BoundedTaylor64 source_domain center_value center_gradient
         value_bound gradient_bounds source_hessian => center_value)
    center_sqrt /\
  bounded_interval64_positive_sqrt_certificate_decimal
    (case source of
     | BoundedTaylor64 source_domain center_value center_gradient
         value_bound gradient_bounds source_hessian => value_bound)
    box_sqrt /\
  (?center_twice.
     bounded_interval64_add center_sqrt center_sqrt = SOME center_twice /\
     bounded_interval64_positive_inv_certificate_decimal
       center_twice center_derivative) /\
  (?box_twice.
     bounded_interval64_add box_sqrt box_sqrt = SOME box_twice /\
     bounded_interval64_positive_inv_certificate_decimal
       box_twice box_derivative) /\
  bounded_taylor64_unary_complete_decimal radii T center_sqrt
    center_derivative box_derivative
    (bounded_interval64_neg box_second_reciprocal) source = SOME result
Proof
  Cases_on `source`
  >> rw
       [compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_def]
QED

Theorem bounded_interval64_self_outer_decimal_length_six:
  LENGTH values = 6 /\
  bounded_interval64_self_outer_decimal values = SOME result ==>
  LENGTH result = 21
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> fs
       [compute_boundedTaylorUnaryDecimalTheory.bounded_interval64_self_outer_decimal_def,
        compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_taylor_sqrt_decimal_typed_contract:
  LENGTH radii = 6 /\
  bounded_hessian64_rows source_hessian = SOME source_hessian_rows /\
  bounded_taylor64_sqrt_decimal radii center_sqrt box_sqrt
      center_derivative box_derivative box_second_reciprocal
      (BoundedTaylor64 T center_value center_gradient value_bound
        gradient_bounds source_hessian) = SOME result ==>
  ?center_twice box_twice result_center_gradient compact_outer outer_rows
   outer_hessian outer_hessian_rows scaled_hessian scaled_hessian_rows
   result_hessian result_rows.
    bounded_interval64_valid center_value /\
    bounded_interval64_valid value_bound /\
    (case center_sqrt of
     | BoundedInterval64 lower upper =>
         bounded_signed64_strict_positive lower /\
         bounded_signed64_strict_positive upper) /\
    (case box_sqrt of
     | BoundedInterval64 lower upper =>
         bounded_signed64_strict_positive lower /\
         bounded_signed64_strict_positive upper) /\
    bounded_interval64_add center_sqrt center_sqrt = SOME center_twice /\
    bounded_interval64_add box_sqrt box_sqrt = SOME box_twice /\
    (case center_twice of
     | BoundedInterval64 lower upper =>
         bounded_signed64_strict_positive lower /\
         bounded_signed64_strict_positive upper) /\
    (case box_twice of
     | BoundedInterval64 lower upper =>
         bounded_signed64_strict_positive lower /\
         bounded_signed64_strict_positive upper) /\
    bounded_interval64_positive_inv_certificate_decimal
      center_twice center_derivative /\
    bounded_interval64_positive_inv_certificate_decimal
      box_twice box_derivative /\
    (case center_derivative of
     | BoundedInterval64 lower upper =>
         bounded_signed64_strict_positive lower /\
         bounded_signed64_strict_positive upper) /\
    (case box_derivative of
     | BoundedInterval64 lower upper =>
         bounded_signed64_strict_positive lower /\
         bounded_signed64_strict_positive upper) /\
    LENGTH center_gradient = 6 /\
    LENGTH gradient_bounds = 6 /\
    bounded_interval64_list_scale_decimal center_derivative
      center_gradient = SOME result_center_gradient /\
    bounded_interval64_self_outer_decimal gradient_bounds =
      SOME compact_outer /\
    bounded_hessian64_rows compact_outer = SOME outer_rows /\
    bounded_interval64_list_scale_decimal
      (bounded_interval64_neg box_second_reciprocal) compact_outer =
        SOME outer_hessian /\
    bounded_hessian64_rows outer_hessian = SOME outer_hessian_rows /\
    bounded_interval64_list_scale_decimal box_derivative source_hessian =
      SOME scaled_hessian /\
    bounded_hessian64_rows scaled_hessian = SOME scaled_hessian_rows /\
    bounded_interval64_list_add outer_hessian scaled_hessian =
      SOME result_hessian /\
    bounded_hessian64_rows result_hessian = SOME result_rows /\
    bounded_object_fs_taylor_complete radii T center_sqrt
      result_center_gradient result_hessian result_rows =
      SOME (bounded_taylor64_rows_object_cv result result_rows)
Proof
  strip_tac
  >> drule registered_case10173_taylor_sqrt_decimal_components
  >> strip_tac
  >> drule
       compute_boundedObjectTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_object_trace
  >> strip_tac
  >> gvs []
  >> imp_res_tac bounded_interval64_positive_sqrt_certificate_output_strict
  >> imp_res_tac bounded_interval64_positive_inv_certificate_strict
  >> imp_res_tac
       compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_sound
  >> imp_res_tac
       compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_nonnegative
  >> imp_res_tac
       compute_registeredCase10173ActualSqrtDerivativeEvalTheory.bounded_interval64_self_add_strict_positive
  >> fs [compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def]
  >> imp_res_tac bounded_interval64_self_outer_decimal_length_six
  >> imp_res_tac
       compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_length
  >> imp_res_tac
       compute_boundedIntervalListTheory.bounded_interval64_list_add_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> `?outer_rows.
        bounded_hessian64_rows gradient_outer = SOME outer_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `?outer_hessian_rows.
        bounded_hessian64_rows outer_hessian = SOME outer_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `?scaled_hessian_rows.
        bounded_hessian64_rows source_hessian_scaled =
          SOME scaled_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `?result_rows.
        bounded_hessian64_rows hessian = SOME result_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> qexistsl_tac
       [`outer_rows`,`outer_hessian_rows`,`scaled_hessian_rows`,`result_rows`]
  >> asm_rewrite_tac []
  >> metis_tac []
QED

val _ = export_theory ();
