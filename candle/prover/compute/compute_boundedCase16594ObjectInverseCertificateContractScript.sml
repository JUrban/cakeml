(*****************************************************************************
 * Exact contract of the first genuine case-16594 inverse packet.
 *
 * Closed arithmetic is paid once for the center certificate.  The box input
 * is representation-equivalent to the center because the preceding source
 * is constant, so its contract is transported without another reduction.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseCertificateContract
Ancestors
  compute_boundedCase16594ObjectInverseCertificateIdentity
  compute_boundedCase16594ObjectSource6SemanticShape
  compute_boundedObjectExactCertificateEquivalence
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_inverse_center_reciprocal_exact:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_taylor_center
      bounded_case16594_object_source6_result)
    bounded_case16594_object_cell0_inverse_center_reciprocal_cv
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_center_identity,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_root_cv_def,
     compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_box_reciprocal_exact:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source6_result)
    bounded_case16594_object_cell0_inverse_box_reciprocal_cv
Proof
  match_mp_tac
    (Q.SPECL
      [`bounded_object_q_taylor_value_bound
          bounded_case16594_object_source6_result`,
       `bounded_object_q_taylor_center
          bounded_case16594_object_source6_result`,
       `bounded_case16594_object_cell0_inverse_box_reciprocal_cv`]
      compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_positive_inv_certificate_exact_equiv_input)
  >> simp
       [compute_boundedCase16594ObjectSource6SemanticShapeTheory.bounded_case16594_object_source6_value_bound_center_equiv,
        compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_reciprocals_identical,
        bounded_case16594_object_inverse_center_reciprocal_exact]
QED

Theorem bounded_case16594_object_inverse_certificate_contract:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_taylor_center
      bounded_case16594_object_source6_result)
    bounded_case16594_object_cell0_inverse_center_reciprocal_cv /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source6_result)
    bounded_case16594_object_cell0_inverse_box_reciprocal_cv
Proof
  simp
    [bounded_case16594_object_inverse_center_reciprocal_exact,
     bounded_case16594_object_inverse_box_reciprocal_exact]
QED

val _ = export_theory ();
