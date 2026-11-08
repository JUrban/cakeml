(*****************************************************************************
 * Exact contract of the first genuine case-16594 sqrt certificate packet.
 *
 * All five certificates are the first five records mechanically split from
 * the authenticated 134-record production payload.  Closed arithmetic is
 * discharged directly; representation transport is explicit where source-5
 * value recompletion produces a non-canonical encoding of the same rational.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtCertificateContract
Ancestors
  compute_boundedCase16594ObjectSqrtCertificateIdentity
  compute_boundedCase16594ObjectSource5SemanticShape
  compute_boundedObjectExactCertificateEquivalence
  compute_boundedCase16594ObjectMulRelation
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_sqrt_center_root_exact:
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_center
      bounded_case16594_object_source5_result)
    bounded_case16594_object_cell0_sqrt_center_root_cv
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectSource5SemanticShapeTheory.bounded_case16594_object_source5_center_identity,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_root_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_box_root_center_exact:
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_center
      bounded_case16594_object_source5_result)
    bounded_case16594_object_cell0_sqrt_box_root_cv
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectSource5SemanticShapeTheory.bounded_case16594_object_source5_center_identity,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_root_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_box_root_exact:
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source5_result)
    bounded_case16594_object_cell0_sqrt_box_root_cv
Proof
  match_mp_tac
    (Q.SPECL
      [`bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result`,
       `bounded_object_q_taylor_center
          bounded_case16594_object_source5_result`,
       `bounded_case16594_object_cell0_sqrt_box_root_cv`]
      compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_sqrt_certificate_exact_equiv_input)
  >> simp
       [compute_boundedCase16594ObjectSource5SemanticShapeTheory.bounded_case16594_object_source5_value_bound_center_equiv,
        bounded_case16594_object_sqrt_box_root_center_exact]
QED

Theorem bounded_case16594_object_sqrt_center_derivative_exact:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv
      bounded_case16594_object_cell0_sqrt_center_root_cv
      bounded_case16594_object_cell0_sqrt_center_root_cv)
    bounded_case16594_object_cell0_sqrt_center_derivative_cv
Proof
  rw
    [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_derivative_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_box_derivative_exact:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv)
    bounded_case16594_object_cell0_sqrt_box_derivative_cv
Proof
  rw
    [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_derivative_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_box_root_encoded:
  bounded_object_q_interval_encoded
    bounded_case16594_object_cell0_sqrt_box_root_cv
Proof
  rw
    [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_root_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem bounded_case16594_object_sqrt_box_twice_equiv_refl:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_add_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv)
    (bounded_object_q_interval_add_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv)
Proof
  irule
    compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
  >> simp [bounded_case16594_object_sqrt_box_root_encoded]
QED

Theorem bounded_case16594_object_source5_value_twice_center_twice_equiv:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_add_cv
      (bounded_object_q_taylor_value_bound
        bounded_case16594_object_source5_result)
      (bounded_object_q_taylor_value_bound
        bounded_case16594_object_source5_result))
    (bounded_object_q_interval_add_cv
      (bounded_object_q_taylor_center
        bounded_case16594_object_source5_result)
      (bounded_object_q_taylor_center
        bounded_case16594_object_source5_result))
Proof
  irule
    compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong
  >> simp
       [compute_boundedCase16594ObjectSource5SemanticShapeTheory.bounded_case16594_object_source5_value_bound_center_equiv]
QED

Theorem bounded_case16594_object_sqrt_box_second_input_equiv:
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result)
        (bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result)))
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_center
          bounded_case16594_object_source5_result)
        (bounded_object_q_taylor_center
          bounded_case16594_object_source5_result)))
Proof
  irule
    compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong
  >> simp
       [bounded_case16594_object_sqrt_box_twice_equiv_refl,
        bounded_case16594_object_source5_value_twice_center_twice_equiv]
QED

Theorem bounded_case16594_object_sqrt_box_second_reciprocal_center_exact:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_center
          bounded_case16594_object_source5_result)
        (bounded_object_q_taylor_center
          bounded_case16594_object_source5_result)))
    bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
Proof
  rw
    [compute_boundedCase16594ObjectSource5SemanticShapeTheory.bounded_case16594_object_source5_center_identity,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_box_second_reciprocal_exact:
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result)
        (bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result)))
    bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
Proof
  match_mp_tac
    (Q.SPECL
      [`bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv)
          (bounded_object_q_interval_add_cv
            (bounded_object_q_taylor_value_bound
              bounded_case16594_object_source5_result)
            (bounded_object_q_taylor_value_bound
              bounded_case16594_object_source5_result))`,
       `bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv)
          (bounded_object_q_interval_add_cv
            (bounded_object_q_taylor_center
              bounded_case16594_object_source5_result)
            (bounded_object_q_taylor_center
              bounded_case16594_object_source5_result))`,
       `bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv`]
      compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_positive_inv_certificate_exact_equiv_input)
  >> simp
       [bounded_case16594_object_sqrt_box_second_input_equiv,
        bounded_case16594_object_sqrt_box_second_reciprocal_center_exact]
QED

Theorem bounded_case16594_object_sqrt_certificate_contract:
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_center
      bounded_case16594_object_source5_result)
    bounded_case16594_object_cell0_sqrt_center_root_cv /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv
      bounded_case16594_object_cell0_sqrt_center_root_cv
      bounded_case16594_object_cell0_sqrt_center_root_cv)
    bounded_case16594_object_cell0_sqrt_center_derivative_cv /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source5_result)
    bounded_case16594_object_cell0_sqrt_box_root_cv /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv)
    bounded_case16594_object_cell0_sqrt_box_derivative_cv /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result)
        (bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result)))
    bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
Proof
  simp
    [bounded_case16594_object_sqrt_center_root_exact,
     bounded_case16594_object_sqrt_center_derivative_exact,
     bounded_case16594_object_sqrt_box_root_exact,
     bounded_case16594_object_sqrt_box_derivative_exact,
     bounded_case16594_object_sqrt_box_second_reciprocal_exact]
QED

val _ = export_theory ()
