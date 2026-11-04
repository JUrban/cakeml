(*****************************************************************************
 * Transport the authenticated source-5 square-root certificate packet from
 * semantic interval encodings to any equivalent production runtime state.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtRuntimeCertificateContract
Ancestors
  compute_boundedCase16594ObjectSqrtCertificateRuntimeEval
Libs
  bossLib preamble

Theorem bounded_case16594_object_runtime_sqrt_center_root_exact:
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source5_result) ==>
  bounded_object_q_sqrt_certificate_exact runtime_center
    bounded_case16594_object_cell0_sqrt_center_root_cv
Proof
  strip_tac
  >> irule
       compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_sqrt_certificate_exact_equiv_input
  >> qexists_tac
       `bounded_object_q_taylor_center
          bounded_case16594_object_source5_result`
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_center_root_exact]
QED

Theorem bounded_case16594_object_runtime_sqrt_box_root_exact:
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source5_result) ==>
  bounded_object_q_sqrt_certificate_exact runtime_value_bound
    bounded_case16594_object_cell0_sqrt_box_root_cv
Proof
  strip_tac
  >> irule
       compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_sqrt_certificate_exact_equiv_input
  >> qexists_tac
       `bounded_object_q_taylor_value_bound
          bounded_case16594_object_source5_result`
  >> simp
       [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_root_exact]
QED

Theorem bounded_case16594_object_runtime_sqrt_box_second_reciprocal_exact:
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source5_result) ==>
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv
        bounded_case16594_object_cell0_sqrt_box_root_cv)
      (bounded_object_q_interval_add_cv
        runtime_value_bound runtime_value_bound))
    bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
Proof
  strip_tac
  >> irule
       compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_positive_inv_certificate_exact_equiv_input
  >> qexists_tac
       `bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv
            bounded_case16594_object_cell0_sqrt_box_root_cv)
          (bounded_object_q_interval_add_cv
            (bounded_object_q_taylor_value_bound
              bounded_case16594_object_source5_result)
            (bounded_object_q_taylor_value_bound
              bounded_case16594_object_source5_result))`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong
      >> simp
           [compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_twice_equiv_refl]
      >> irule
           compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong
      >> simp [])
  >> ACCEPT_TAC
       compute_boundedCase16594ObjectSqrtCertificateContractTheory.bounded_case16594_object_sqrt_box_second_reciprocal_exact
QED

val _ = export_theory ();
