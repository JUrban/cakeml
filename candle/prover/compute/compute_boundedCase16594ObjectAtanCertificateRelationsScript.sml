(*****************************************************************************
 * Representation identities inside the first genuine atan certificate.
 *
 * The input to this atan is constant.  The producer therefore emitted the
 * same interval for the center and box paths, and the same derived square
 * and reciprocal intervals.  These are authenticated data equalities, not
 * assumptions about the semantic expression.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanCertificateRelations
Ancestors
  compute_boundedCase16594ObjectAtanCertificateIdentity
Libs
  bossLib preamble

Theorem bounded_case16594_object_atan_inputs_identical:
  bounded_case16594_object_cell0_atan_box_input_cv =
    bounded_case16594_object_cell0_atan_center_input_cv
Proof
  simp
    [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_input_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_input_cv_def]
QED

Theorem bounded_case16594_object_atan_squares_identical:
  bounded_case16594_object_cell0_atan_box_square_cv =
    bounded_case16594_object_cell0_atan_center_square_cv
Proof
  simp
    [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_square_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_square_cv_def]
QED

Theorem bounded_case16594_object_atan_derivatives_identical:
  bounded_case16594_object_cell0_atan_box_derivative_cv =
    bounded_case16594_object_cell0_atan_center_derivative_cv
Proof
  simp
    [compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_box_derivative_cv_def,
     compute_boundedCase16594ObjectAtanCertificateIdentityTheory.bounded_case16594_object_cell0_atan_center_derivative_cv_def]
QED

val _ = export_theory ();
