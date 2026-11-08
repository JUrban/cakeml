(*****************************************************************************
 * Genuine case-16594 instantiation of the complete production inverse step.
 * The theorem consumes the authenticated post-sqrt certificate stream and
 * applies to any runtime source-6 state related to its exact semantics.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseStepRuntimeEval
Ancestors
  compute_boundedCase16594ObjectInverseStepCompleteEval
  compute_boundedCase16594ObjectInverseCertificateContract
  compute_boundedCase16594ObjectSqrtStepRuntimeEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_after_inverse_certificates_encode:
  ?certificate_rest.
    bounded_object_q_cv_list certificate_rest =
      bounded_case16594_object_cell0_after_inverse_certificates_cv
Proof
  qexists_tac
    `THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_after_inverse_certificates_cv)`
  >> irule
       compute_boundedPackedObjectEntryRefinementTheory.bounded_object_q_cv_list_encode_decode
  >> rewrite_tac
       [compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_after_inverse_certificates_cv_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_certificate_outputs_encoded:
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_inverse_center_reciprocal_cv /\
  bounded_object_q_interval_encoded
      bounded_case16594_object_cell0_inverse_box_reciprocal_cv
Proof
  rw
    [compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def,
     compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_box_reciprocal_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem bounded_case16594_object_runtime_inverse_center_exact:
  bounded_object_q_interval_cv_equiv runtime_center
    (bounded_object_q_taylor_center
      bounded_case16594_object_source6_result) ==>
  bounded_object_q_positive_inv_certificate_exact runtime_center
    bounded_case16594_object_cell0_inverse_center_reciprocal_cv
Proof
  strip_tac
  >> irule
       compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_positive_inv_certificate_exact_equiv_input
  >> qexists_tac
       `bounded_object_q_taylor_center
          bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectInverseCertificateContractTheory.bounded_case16594_object_inverse_center_reciprocal_exact]
QED

Theorem bounded_case16594_object_runtime_inverse_box_exact:
  bounded_object_q_interval_cv_equiv runtime_value_bound
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source6_result) ==>
  bounded_object_q_positive_inv_certificate_exact runtime_value_bound
    bounded_case16594_object_cell0_inverse_box_reciprocal_cv
Proof
  strip_tac
  >> irule
       compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_positive_inv_certificate_exact_equiv_input
  >> qexists_tac
       `bounded_object_q_taylor_value_bound
          bounded_case16594_object_source6_result`
  >> simp
       [compute_boundedCase16594ObjectInverseCertificateContractTheory.bounded_case16594_object_inverse_box_reciprocal_exact]
QED

Theorem bounded_case16594_object_genuine_inverse_step_eval:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source6_result /\
  8210 < clock ==>
  ?runtime_domain runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime_item =
      bounded_case16594_object_state_cv runtime_domain runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_inv_step»
          [from_cv bounded_case16594_object_cell0_radii_cv;
           from_cv
             bounded_case16594_object_cell0_after_sqrt_certificates_cv;
           from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
      (M_success
        (Pair (Num 1)
          (Pair
            (Pair
              (from_cv
                (bounded_case16594_object_state_unary_cv
                  bounded_case16594_object_cell0_runtime_radii
                  runtime_domain
                  bounded_case16594_object_cell0_inverse_center_reciprocal_cv
                  (bounded_object_q_interval_neg_cv
                    (bounded_object_q_interval_mul_cv
                      bounded_case16594_object_cell0_inverse_center_reciprocal_cv
                      bounded_case16594_object_cell0_inverse_center_reciprocal_cv))
                  (bounded_object_q_interval_neg_cv
                    (bounded_object_q_interval_mul_cv
                      bounded_case16594_object_cell0_inverse_box_reciprocal_cv
                      bounded_case16594_object_cell0_inverse_box_reciprocal_cv))
                  (bounded_object_q_interval_add_cv
                    (bounded_object_q_interval_mul_cv
                      (bounded_object_q_interval_mul_cv
                        bounded_case16594_object_cell0_inverse_box_reciprocal_cv
                        bounded_case16594_object_cell0_inverse_box_reciprocal_cv)
                      bounded_case16594_object_cell0_inverse_box_reciprocal_cv)
                    (bounded_object_q_interval_mul_cv
                      (bounded_object_q_interval_mul_cv
                        bounded_case16594_object_cell0_inverse_box_reciprocal_cv
                        bounded_case16594_object_cell0_inverse_box_reciprocal_cv)
                      bounded_case16594_object_cell0_inverse_box_reciprocal_cv))
                  runtime_center_gradient runtime_gradient_bounds
                  runtime_hessian))
              (from_cv stack_rest))
            (from_cv
              bounded_case16594_object_cell0_after_inverse_certificates_cv))),
       refs)
Proof
  strip_tac
  >> drule
       compute_boundedCase16594ObjectSqrtStepRuntimeEvalTheory.bounded_case16594_object_runtime_refines_selector_contract
  >> disch_then
       (qx_choose_then `runtime_domain`
         (qx_choose_then `runtime_center`
           (qx_choose_then `runtime_center_gradient`
             (qx_choose_then `runtime_value_bound`
               (qx_choose_then `runtime_gradient_bounds`
                 (qx_choose_then `runtime_hessian` strip_assume_tac))))))
  >> mp_tac bounded_case16594_object_after_inverse_certificates_encode
  >> disch_then (qx_choose_then `certificate_rest` assume_tac)
  >> qexists_tac `runtime_domain`
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> conj_tac
  >> TRY (asm_rewrite_tac [])
  >> PURE_REWRITE_TAC
       [GSYM
          compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encode,
        compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_certificates_inverse_split]
  >> qpat_x_assum
       `bounded_object_q_cv_list certificate_rest =
          bounded_case16594_object_cell0_after_inverse_certificates_cv`
       (fn th => PURE_REWRITE_TAC [GSYM th])
  >> irule
       (PURE_REWRITE_RULE
         [listTheory.APPEND,
          compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
         compute_boundedCase16594ObjectInverseStepCompleteEvalTheory.bounded_case16594_object_inverse_step_eval)
  >> simp
       [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encoded,
        compute_boundedCase16594ObjectFirstPolyRunBridgeTheory.bounded_case16594_object_source0_runtime_radii_length,
        bounded_case16594_object_inverse_certificate_outputs_encoded,
        compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed]
  >> fs [listTheory.EVERY_MEM]
  >> metis_tac
       [compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed,
        bounded_case16594_object_runtime_inverse_center_exact,
        bounded_case16594_object_runtime_inverse_box_exact]
QED

val _ = export_theory ();
