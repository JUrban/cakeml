(*****************************************************************************
 * Exact algebraic contract of the first genuine case-16594 atan packet.
 *
 * The transcendental result certificate is intentionally kept separate.
 * This file discharges the two input squares, two reciprocal derivatives,
 * and the derivative square against the authenticated genuine records.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanCertificateContract
Ancestors
  compute_boundedCase16594ObjectAtanInputContract
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_atan_center_square_exact:
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_center bounded_case16594_object_source8_result)
    bounded_case16594_object_cell0_atan_center_input_cv
    bounded_case16594_object_cell0_atan_center_square_cv
Proof
  rw
    [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_square_certificate_exact_def]
  >- ACCEPT_TAC
       compute_boundedCase16594ObjectSource8SemanticShapeTheory.bounded_case16594_object_source8_center_certificate_encloses
  >> rw
       [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_input_cv_def,
        compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_square_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_box_square_exact:
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result)
    bounded_case16594_object_cell0_atan_box_input_cv
    bounded_case16594_object_cell0_atan_box_square_cv
Proof
  rw
    [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_square_certificate_exact_def]
  >- ACCEPT_TAC bounded_case16594_object_source8_value_bound_certificate_encloses
  >> rw
       [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_input_cv_def,
        compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_square_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_center_derivative_exact:
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv
      bounded_case16594_object_cell0_atan_center_square_cv)
    bounded_case16594_object_cell0_atan_center_derivative_cv
Proof
  rw
    [compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_object_q_inv_certificate_exact_def,
     compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_denominator_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_square_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_derivative_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_box_derivative_exact:
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv
      bounded_case16594_object_cell0_atan_box_square_cv)
    bounded_case16594_object_cell0_atan_box_derivative_cv
Proof
  rw
    [compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_object_q_inv_certificate_exact_def,
     compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_denominator_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_square_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_box_derivative_square_exact:
  bounded_object_q_square_certificate_exact
    bounded_case16594_object_cell0_atan_box_derivative_cv
    bounded_case16594_object_cell0_atan_box_derivative_cv
    bounded_case16594_object_cell0_atan_box_derivative_square_cv
Proof
  rw
    [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_square_certificate_exact_def,
     compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_interval_encloses_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_square_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_algebraic_certificate_contract:
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_center bounded_case16594_object_source8_result)
    bounded_case16594_object_cell0_atan_center_input_cv
    bounded_case16594_object_cell0_atan_center_square_cv /\
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source8_result)
    bounded_case16594_object_cell0_atan_box_input_cv
    bounded_case16594_object_cell0_atan_box_square_cv /\
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv
      bounded_case16594_object_cell0_atan_center_square_cv)
    bounded_case16594_object_cell0_atan_center_derivative_cv /\
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv
      bounded_case16594_object_cell0_atan_box_square_cv)
    bounded_case16594_object_cell0_atan_box_derivative_cv /\
  bounded_object_q_square_certificate_exact
    bounded_case16594_object_cell0_atan_box_derivative_cv
    bounded_case16594_object_cell0_atan_box_derivative_cv
    bounded_case16594_object_cell0_atan_box_derivative_square_cv
Proof
  simp
    [bounded_case16594_object_atan_center_square_exact,
     bounded_case16594_object_atan_box_square_exact,
     bounded_case16594_object_atan_center_derivative_exact,
     bounded_case16594_object_atan_box_derivative_exact,
     bounded_case16594_object_atan_box_derivative_square_exact]
QED

val _ = export_theory ();
