(*****************************************************************************
 * Semantic preservation for the first genuine production inverse step.
 * The evaluator and certificate packet are already authenticated; this
 * theory connects the returned state to the universal object-q Taylor
 * inverse semantics.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseStepSemanticEval
Ancestors
  compute_boundedCase16594ObjectInverseStepRuntimeEval
  compute_boundedCase16594ObjectUnaryRelation
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_source7_result_def:
  bounded_case16594_object_source7_result =
    bounded_object_q_taylor_inverse
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      bounded_case16594_object_cell0_inverse_center_reciprocal_cv
      bounded_case16594_object_cell0_inverse_box_reciprocal_cv
      bounded_case16594_object_source6_result
End

Theorem bounded_case16594_object_inverse_certificate_outputs_valid:
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_inverse_center_reciprocal_cv /\
  bounded_packed_q_interval_valid_cv
      bounded_case16594_object_cell0_inverse_box_reciprocal_cv
Proof
  rw
    [compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_center_reciprocal_cv_def,
     compute_boundedCase16594ObjectInverseCertificateIdentityTheory.bounded_case16594_object_cell0_inverse_box_reciprocal_cv_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> EVAL_TAC
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_object_inverse_unary_outputs_valid:
  bounded_packed_q_interval_valid_cv center_reciprocal /\
  bounded_packed_q_interval_valid_cv box_reciprocal ==>
  bounded_packed_q_interval_valid_cv center_reciprocal /\
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_neg_cv
      (bounded_object_q_interval_mul_cv
        center_reciprocal center_reciprocal)) /\
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_neg_cv
      (bounded_object_q_interval_mul_cv
        box_reciprocal box_reciprocal)) /\
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_add_cv
      (bounded_object_q_interval_mul_cv
        (bounded_object_q_interval_mul_cv
          box_reciprocal box_reciprocal) box_reciprocal)
      (bounded_object_q_interval_mul_cv
        (bounded_object_q_interval_mul_cv
          box_reciprocal box_reciprocal) box_reciprocal))
Proof
  strip_tac
  >> metis_tac
       [compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add]
QED

Theorem bounded_case16594_object_source7_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    bounded_case16594_object_source7_result
Proof
  rewrite_tac
    [bounded_case16594_object_source7_result_def,
     compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_inverse_def]
  >> irule
       compute_boundedCase16594ObjectUnaryRelationTheory.bounded_object_q_taylor_unary_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
        compute_boundedCase16594ObjectSqrtStepSemanticEvalTheory.bounded_case16594_object_source6_semantic_valid,
        bounded_case16594_object_inverse_certificate_outputs_valid]
  >> mp_tac bounded_case16594_object_inverse_certificate_outputs_valid
  >> metis_tac
       [compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add]
QED

Theorem bounded_case16594_object_inverse_unary_inputs_equiv_refl:
  bounded_object_q_interval_cv_equiv
      bounded_case16594_object_cell0_inverse_center_reciprocal_cv
      bounded_case16594_object_cell0_inverse_center_reciprocal_cv /\
  bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          bounded_case16594_object_cell0_inverse_center_reciprocal_cv
          bounded_case16594_object_cell0_inverse_center_reciprocal_cv))
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          bounded_case16594_object_cell0_inverse_center_reciprocal_cv
          bounded_case16594_object_cell0_inverse_center_reciprocal_cv)) /\
  bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          bounded_case16594_object_cell0_inverse_box_reciprocal_cv
          bounded_case16594_object_cell0_inverse_box_reciprocal_cv))
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          bounded_case16594_object_cell0_inverse_box_reciprocal_cv
          bounded_case16594_object_cell0_inverse_box_reciprocal_cv)) /\
  bounded_object_q_interval_cv_equiv
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
Proof
  mp_tac bounded_case16594_object_inverse_certificate_outputs_valid
  >> strip_tac
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv
            bounded_case16594_object_cell0_inverse_center_reciprocal_cv
            bounded_case16594_object_cell0_inverse_center_reciprocal_cv)) /\
      bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv
            bounded_case16594_object_cell0_inverse_box_reciprocal_cv
            bounded_case16594_object_cell0_inverse_box_reciprocal_cv)) /\
      bounded_packed_q_interval_valid_cv
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
            bounded_case16594_object_cell0_inverse_box_reciprocal_cv))` by
       metis_tac
         [compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
          compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul,
          compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add]
  >> rpt conj_tac
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
  >> metis_tac
       [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_genuine_inverse_decomposition_refines:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source6_result /\
  runtime_item =
    bounded_case16594_object_state_cv runtime_domain runtime_center
      (bounded_object_q_cv_list runtime_center_gradient)
      runtime_value_bound
      (bounded_object_q_cv_list runtime_gradient_bounds)
      (bounded_object_q_cv_list runtime_hessian) ==>
  runtime_domain =
    (if bounded_object_q_taylor_domain
          bounded_case16594_object_source6_result
     then Num 1 else Num 0) /\
  bounded_object_q_taylor_runtime_refines
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
      runtime_center_gradient runtime_gradient_bounds runtime_hessian)
    bounded_case16594_object_source7_result
Proof
  Cases_on `bounded_case16594_object_source6_result`
  >> strip_tac
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_encoded_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def,
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_domain_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_cv_equiv_encoded]
  >> conj_tac
  >- (asm_simp_tac std_ss
        [bounded_case16594_object_source7_result_def,
         compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_inverse_def]
      >> qpat_x_assum
           `BoundedObjectQTaylor b c l c0 l0 l1 =
              bounded_case16594_object_source6_result`
           (assume_tac o GSYM)
      >> asm_rewrite_tac []
      >> irule
           (REWRITE_RULE
             [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def]
             compute_boundedCase16594ObjectUnaryRelationTheory.bounded_case16594_object_unary_runtime_semantic_equiv)
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
      >> simp
           [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
            compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_equivalent,
            bounded_case16594_object_inverse_certificate_outputs_valid,
            bounded_case16594_object_inverse_unary_outputs_valid,
            bounded_case16594_object_inverse_unary_inputs_equiv_refl]
      >> mp_tac bounded_case16594_object_inverse_certificate_outputs_valid
      >> metis_tac
           [compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
            compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul,
            compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add])
  >> ACCEPT_TAC bounded_case16594_object_source7_semantic_valid
QED

Theorem bounded_case16594_object_genuine_inverse_step_eval_semantic:
  bounded_object_q_taylor_runtime_refines runtime_item
      bounded_case16594_object_source6_result /\
  8210 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inv_step»
        [from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv
           bounded_case16594_object_cell0_after_sqrt_certificates_cv;
         from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair (from_cv runtime_result) (from_cv stack_rest))
          (from_cv
            bounded_case16594_object_cell0_after_inverse_certificates_cv))),
     refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      bounded_case16594_object_source7_result
Proof
  strip_tac
  >> mp_tac
       compute_boundedCase16594ObjectInverseStepRuntimeEvalTheory.bounded_case16594_object_genuine_inverse_step_eval
  >> impl_tac
  >- simp []
  >> strip_tac
  >> mp_tac bounded_case16594_object_genuine_inverse_decomposition_refines
  >> impl_tac
  >- simp []
  >> strip_tac
  >> qexists_tac
       `bounded_case16594_object_state_unary_cv
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
          runtime_center_gradient runtime_gradient_bounds runtime_hessian`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
