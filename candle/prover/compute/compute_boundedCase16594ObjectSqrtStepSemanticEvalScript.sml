(*****************************************************************************
 * Semantic preservation for the first genuine production square-root step.
 *
 * The numerical certificate packet and evaluator trace are already proved;
 * this theory connects their returned runtime state to the object-q Taylor
 * semantics used by the universal analytic soundness theorem.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtStepSemanticEval
Ancestors
  compute_boundedCase16594ObjectSqrtStepRuntimeEval
  compute_boundedCase16594ObjectUnaryRelation
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_source6_result_def:
  bounded_case16594_object_source6_result =
    bounded_object_q_taylor_sqrt
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      bounded_case16594_object_cell0_sqrt_center_root_cv
      bounded_case16594_object_cell0_sqrt_center_derivative_cv
      bounded_case16594_object_cell0_sqrt_box_derivative_cv
      bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
      bounded_case16594_object_source5_result
End

Theorem bounded_case16594_object_sqrt_certificate_outputs_valid:
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_sqrt_center_root_cv /\
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_sqrt_box_root_cv /\
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_sqrt_center_derivative_cv /\
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_sqrt_box_derivative_cv /\
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv
Proof
  rw
    [compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_root_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_center_derivative_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_derivative_cv_def,
     compute_boundedCase16594ObjectSqrtCertificateIdentityTheory.bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_object_sqrt_box_second_valid:
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_neg_cv
      bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv)
Proof
  irule
       compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg
  >> simp [bounded_case16594_object_sqrt_certificate_outputs_valid]
QED

Theorem bounded_case16594_object_source6_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    bounded_case16594_object_source6_result
Proof
  rewrite_tac
    [bounded_case16594_object_source6_result_def,
     compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_sqrt_def]
  >> irule
       compute_boundedCase16594ObjectUnaryRelationTheory.bounded_object_q_taylor_unary_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
        compute_boundedCase16594ObjectSource5SemanticShapeTheory.bounded_case16594_object_source5_semantic_valid,
        bounded_case16594_object_sqrt_certificate_outputs_valid,
        bounded_case16594_object_sqrt_box_second_valid]
QED

Theorem bounded_case16594_object_sqrt_unary_inputs_equiv_refl:
  bounded_object_q_interval_cv_equiv
      bounded_case16594_object_cell0_sqrt_center_root_cv
      bounded_case16594_object_cell0_sqrt_center_root_cv /\
  bounded_object_q_interval_cv_equiv
      bounded_case16594_object_cell0_sqrt_center_derivative_cv
      bounded_case16594_object_cell0_sqrt_center_derivative_cv /\
  bounded_object_q_interval_cv_equiv
      bounded_case16594_object_cell0_sqrt_box_derivative_cv
      bounded_case16594_object_cell0_sqrt_box_derivative_cv /\
  bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_neg_cv
        bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv)
      (bounded_object_q_interval_neg_cv
        bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv)
Proof
  mp_tac bounded_case16594_object_sqrt_certificate_outputs_valid
  >> strip_tac
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_neg_cv
          bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv)` by
       simp [bounded_case16594_object_sqrt_box_second_valid]
  >> rpt conj_tac
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_genuine_sqrt_state_runtime_refines:
  bounded_object_q_taylor_runtime_refines runtime_item
    bounded_case16594_object_source5_result ==>
  ?runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime_item =
      bounded_case16594_object_state_cv
        (if bounded_object_q_taylor_domain
              bounded_case16594_object_source5_result
         then Num 1 else Num 0)
        runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    bounded_object_q_taylor_runtime_refines
      (bounded_case16594_object_state_unary_cv
        bounded_case16594_object_cell0_runtime_radii
        (if bounded_object_q_taylor_domain
              bounded_case16594_object_source5_result
         then Num 1 else Num 0)
        bounded_case16594_object_cell0_sqrt_center_root_cv
        bounded_case16594_object_cell0_sqrt_center_derivative_cv
        bounded_case16594_object_cell0_sqrt_box_derivative_cv
        (bounded_object_q_interval_neg_cv
          bounded_case16594_object_cell0_sqrt_box_second_reciprocal_cv)
        runtime_center_gradient runtime_gradient_bounds runtime_hessian)
      bounded_case16594_object_source6_result
Proof
  Cases_on `bounded_case16594_object_source5_result`
  >> strip_tac
  >> drule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_contract
  >> disch_then
       (qx_choose_then `runtime_center`
         (qx_choose_then `runtime_center_gradient`
           (qx_choose_then `runtime_value_bound`
             (qx_choose_then `runtime_gradient_bounds`
               (qx_choose_then `runtime_hessian` strip_assume_tac)))))
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> conj_tac
  >- fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def]
  >> rewrite_tac
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def]
  >> conj_tac
  >- (asm_simp_tac std_ss
        [bounded_case16594_object_source6_result_def,
         compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_sqrt_def,
         compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def]
      >> irule
           compute_boundedCase16594ObjectUnaryRelationTheory.bounded_case16594_object_unary_runtime_semantic_equiv
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
      >> simp
           [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
            compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_equivalent,
            bounded_case16594_object_sqrt_certificate_outputs_valid,
            bounded_case16594_object_sqrt_box_second_valid,
            bounded_case16594_object_sqrt_unary_inputs_equiv_refl])
  >> ACCEPT_TAC bounded_case16594_object_source6_semantic_valid
QED

val _ = export_theory ();
