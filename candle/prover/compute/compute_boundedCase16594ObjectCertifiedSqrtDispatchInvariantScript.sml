(*****************************************************************************
 * Generic production-dispatch refinement for exact square-root certificates.
 *
 * All five certificate obligations are stated against the semantic source
 * state and transported to any related production runtime state.  The
 * resulting theorem consumes exactly those five records and preserves the
 * residual certificate cursor.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectCertifiedSqrtDispatchInvariant
Ancestors
  compute_boundedCase16594ObjectCertifiedInverseDispatchInvariant
  compute_boundedCase16594ObjectSqrtStepSemanticEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_sqrt_decomposition_runtime_refines:
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv center_root /\
  bounded_packed_q_interval_valid_cv box_root /\
  bounded_packed_q_interval_valid_cv center_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_second_reciprocal /\
  bounded_object_q_taylor_runtime_refines runtime_item semantic_state /\
  runtime_item =
    bounded_case16594_object_state_cv runtime_domain runtime_center
      (bounded_object_q_cv_list runtime_center_gradient)
      runtime_value_bound
      (bounded_object_q_cv_list runtime_gradient_bounds)
      (bounded_object_q_cv_list runtime_hessian) ==>
  runtime_domain =
    (if bounded_object_q_taylor_domain semantic_state
     then Num 1 else Num 0) /\
  bounded_object_q_taylor_runtime_refines
    (compute_boundedCase16594ObjectUnaryCompleteEval$bounded_case16594_object_state_unary_cv
      runtime_radii runtime_domain center_root center_derivative
      box_derivative
      (bounded_object_q_interval_neg_cv box_second_reciprocal)
      runtime_center_gradient runtime_gradient_bounds runtime_hessian)
    (bounded_object_q_taylor_sqrt semantic_radii weights center_root
      center_derivative box_derivative box_second_reciprocal
      semantic_state)
Proof
  Cases_on `semantic_state`
  >> strip_tac
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_neg_cv box_second_reciprocal)` by
       metis_tac
         [compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg]
  >> `bounded_object_q_interval_cv_equiv center_root center_root /\
      bounded_object_q_interval_cv_equiv
        center_derivative center_derivative /\
      bounded_object_q_interval_cv_equiv box_derivative box_derivative /\
      bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_neg_cv box_second_reciprocal)
        (bounded_object_q_interval_neg_cv box_second_reciprocal)` by
       (rpt conj_tac
        >> irule
             compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
        >> metis_tac
             [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded])
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
        [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_sqrt_def]
      >> irule
           (REWRITE_RULE
             [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def]
             compute_boundedCase16594ObjectUnaryRelationTheory.bounded_case16594_object_unary_runtime_semantic_equiv)
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def])
  >> rewrite_tac
       [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_sqrt_def]
  >> irule
       compute_boundedCase16594ObjectUnaryRelationTheory.bounded_object_q_taylor_unary_semantic_valid
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
QED

Theorem bounded_case16594_object_sqrt_step_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv center_root /\
  bounded_packed_q_interval_valid_cv box_root /\
  bounded_packed_q_interval_valid_cv center_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_second_reciprocal /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_center semantic_state) center_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv center_root center_root)
    center_derivative /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_value_bound semantic_state) box_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv box_root box_root)
    box_derivative /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv box_root box_root)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_value_bound semantic_state)
        (bounded_object_q_taylor_value_bound semantic_state)))
    box_second_reciprocal /\
  bounded_object_q_taylor_runtime_refines runtime_item semantic_state /\
  8210 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_sqrt_step»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv
           (bounded_object_q_cv_list
             ([center_root;box_root;center_derivative;box_derivative;
               box_second_reciprocal] ++ certificate_rest));
         from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
      (M_success
        (Pair (Num 1)
          (Pair
            (Pair (from_cv runtime_result) (from_cv stack_rest))
            (from_cv (bounded_object_q_cv_list certificate_rest)))),refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      (bounded_object_q_taylor_sqrt semantic_radii weights center_root
        center_derivative box_derivative box_second_reciprocal
        semantic_state)
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
  >> `bounded_object_q_sqrt_certificate_exact runtime_center center_root /\
      bounded_object_q_sqrt_certificate_exact runtime_value_bound box_root` by
       metis_tac
         [compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_sqrt_certificate_exact_equiv_input]
  >> `bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv box_root box_root)
          (bounded_object_q_interval_add_cv
            runtime_value_bound runtime_value_bound))
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv box_root box_root)
          (bounded_object_q_interval_add_cv
            (bounded_object_q_taylor_value_bound semantic_state)
            (bounded_object_q_taylor_value_bound semantic_state)))` by
       (irule
          compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong
        >> conj_tac
        >- (irule
              compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
            >> metis_tac
                 [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded,
                  compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add])
        >> irule
             compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong
        >> asm_rewrite_tac [])
  >> `bounded_object_q_positive_inv_certificate_exact
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv box_root box_root)
          (bounded_object_q_interval_add_cv
            runtime_value_bound runtime_value_bound))
        box_second_reciprocal` by
       metis_tac
         [compute_boundedObjectExactCertificateEquivalenceTheory.bounded_object_q_positive_inv_certificate_exact_equiv_input]
  >> `bounded_packed_q_interval_encoded center_root /\
      bounded_packed_q_interval_encoded box_root /\
      bounded_packed_q_interval_encoded center_derivative /\
      bounded_packed_q_interval_encoded box_derivative /\
      bounded_packed_q_interval_encoded box_second_reciprocal` by
       metis_tac
         [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded,
          compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed]
  >> mp_tac
       (Q.INST
         [`radii` |-> `runtime_radii`,
          `center_root` |-> `center_root`,
          `box_root` |-> `box_root`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `box_second_reciprocal` |-> `box_second_reciprocal`,
          `center_gradient` |-> `runtime_center_gradient`,
          `gradient_bounds` |-> `runtime_gradient_bounds`,
          `packed_hessian` |-> `runtime_hessian`,
          `center_value` |-> `runtime_center`,
          `value_bound` |-> `runtime_value_bound`,
          `domain_cv` |-> `runtime_domain`,
          `certificate_rest` |-> `certificate_rest`,
          `stack_rest` |-> `stack_rest`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_boundedCase16594ObjectSqrtStepCompleteEvalTheory.bounded_case16594_object_sqrt_step_eval)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> rpt conj_tac
      >> fs [listTheory.EVERY_MEM]
      >> metis_tac
           [compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed])
  >> strip_tac
  >> qexists_tac
       `compute_boundedCase16594ObjectUnaryCompleteEval$bounded_case16594_object_state_unary_cv
          runtime_radii runtime_domain center_root center_derivative
          box_derivative
          (bounded_object_q_interval_neg_cv box_second_reciprocal)
          runtime_center_gradient runtime_gradient_bounds runtime_hessian`
  >> conj_tac
  >- (qpat_x_assum
        `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          _ refs = _` mp_tac
      >> asm_rewrite_tac [])
  >> mp_tac
       (Q.INST
         [`semantic_radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `runtime_radii` |-> `runtime_radii`,
          `center_root` |-> `center_root`,
          `box_root` |-> `box_root`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `box_second_reciprocal` |-> `box_second_reciprocal`,
          `runtime_item` |-> `runtime_item`,
          `semantic_state` |-> `semantic_state`,
          `runtime_domain` |-> `runtime_domain`,
          `runtime_center` |-> `runtime_center`,
          `runtime_center_gradient` |-> `runtime_center_gradient`,
          `runtime_value_bound` |-> `runtime_value_bound`,
          `runtime_gradient_bounds` |-> `runtime_gradient_bounds`,
          `runtime_hessian` |-> `runtime_hessian`]
         bounded_case16594_object_sqrt_decomposition_runtime_refines)
  >> impl_tac
  >- asm_rewrite_tac []
  >> strip_tac
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_sqrt_dispatch_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_packed_q_interval_valid_cv center_root /\
  bounded_packed_q_interval_valid_cv box_root /\
  bounded_packed_q_interval_valid_cv center_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_second_reciprocal /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_center semantic_state) center_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv center_root center_root)
    center_derivative /\
  bounded_object_q_sqrt_certificate_exact
    (bounded_object_q_taylor_value_bound semantic_state) box_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv box_root box_root)
    box_derivative /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv box_root box_root)
      (bounded_object_q_interval_add_cv
        (bounded_object_q_taylor_value_bound semantic_state)
        (bounded_object_q_taylor_value_bound semantic_state)))
    box_second_reciprocal /\
  bounded_object_q_taylor_runtime_refines runtime_item semantic_state /\
  8213 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (Num 0);from_cv (Pair (Num 1) source_payload);
         from_cv
           (bounded_object_q_cv_list
             ([center_root;box_root;center_derivative;box_derivative;
               box_second_reciprocal] ++ certificate_rest));
         from_cv (Pair runtime_item stack_rest)]) (refs:hol_refs) =
      (M_success
        (Pair (Num 1)
          (Pair
            (Pair (from_cv runtime_result) (from_cv stack_rest))
            (from_cv (bounded_object_q_cv_list certificate_rest)))),refs) /\
    bounded_object_q_taylor_runtime_refines runtime_result
      (bounded_object_q_taylor_sqrt semantic_radii weights center_root
        center_derivative box_derivative box_second_reciprocal
        semantic_state)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 3`, `refs` |-> `refs`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`,
          `weights` |-> `weights`,
          `center_root` |-> `center_root`,
          `box_root` |-> `box_root`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `box_second_reciprocal` |-> `box_second_reciprocal`,
          `certificate_rest` |-> `certificate_rest`,
          `runtime_item` |-> `runtime_item`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `stack_rest`]
         bounded_case16594_object_sqrt_step_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_nonzero_pair_eval
      >> conj_tac >- simp []
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectSqrtStepSemanticEvalTheory.bounded_case16594_object_nonpoly_sqrt_control_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> `clock - 1 - 1 - 1 = clock - 3` by intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
