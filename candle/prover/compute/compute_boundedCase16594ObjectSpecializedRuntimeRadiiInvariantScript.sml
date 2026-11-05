(*****************************************************************************
 * Specialized delta refinement under the authenticated runtime radii.
 *
 * The fixed-word semantic radii and the production exact-rational radii are
 * equivalent but not required to have identical cv representations.  These
 * theorems strengthen the six specialized adapters so their evaluator side
 * accepts any encoded runtime radii related to the word-derived semantic
 * radii, while the returned state still refines the exact object-q result.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSpecializedRuntimeRadiiInvariant
Ancestors
  compute_boundedCase16594ObjectSpecializedDispatchStepInvariant
  compute_boundedCase16594ObjectRecompleteRelation
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_product_outer_hessian_runtime_word_rel:
  coordinate < 6 /\
  LENGTH center_boxes = 6 /\
  LENGTH outer_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  EVERY bounded_packed_q_interval_valid_cv outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_delta_gradient_cv
      center_boxes) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_delta_hessian_six_cv
      (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
      (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) ==>
  LIST_REL bounded_object_q_interval_cv_equiv
    (bounded_case16594_object_delta_product_outer_hessian_cv
      runtime_radii center_boxes outer_boxes coordinate)
    (bounded_case16594_object_delta_product_outer_hessian_cv
      (MAP bounded_word64_object_q_cv semantic_radii)
      center_boxes outer_boxes coordinate)
Proof
  strip_tac
  >> qabbrev_tac
       `center_delta_gradient =
          bounded_case16594_object_delta_product_center_delta_gradient_cv
            center_boxes`
  >> qabbrev_tac
       `delta_hessian = bounded_object_q_delta_hessian_six_cv
          (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
          (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)`
  >> qabbrev_tac
       `runtime_gradient = bounded_packed_q_source_gradient_complete6_cv
          runtime_radii center_delta_gradient delta_hessian`
  >> qabbrev_tac
       `word_gradient = bounded_packed_q_source_gradient_complete6_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          center_delta_gradient delta_hessian`
  >> `LENGTH semantic_radii = 6` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> `LENGTH runtime_radii = 6` by
       metis_tac [LIST_REL_LENGTH,rich_listTheory.LENGTH_MAP]
  >> `LENGTH center_delta_gradient = 6` by
       (qunabbrev_tac `center_delta_gradient`
        >> simp
             [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
              compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length])
  >> `LENGTH delta_hessian = 21` by
       (qunabbrev_tac `delta_hessian`
        >> simp
             [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length])
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        center_delta_gradient center_delta_gradient` by
       (irule
          compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
        >> simp [])
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        delta_hessian delta_hessian` by
       (irule
          compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
        >> simp [])
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        runtime_gradient word_gradient` by
       (qunabbrev_tac `runtime_gradient`
        >> qunabbrev_tac `word_gradient`
        >> irule
             compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_complete6_cv_rel
        >> simp [])
  >> `LENGTH runtime_gradient = 6` by
       (qunabbrev_tac `runtime_gradient`
        >> mp_tac
             (Q.INST
               [`radii` |-> `runtime_radii`,
                `center_gradient` |-> `center_delta_gradient`,
                `packed_hessian` |-> `delta_hessian`]
               compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_gradient_complete6_encoded_length)
        >> impl_tac
        >- simp
             [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded]
        >> simp [])
  >> `bounded_object_q_interval_cv_equiv
        (EL coordinate outer_boxes) (EL coordinate outer_boxes)` by
       (irule
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
        >> irule
             compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded
        >> fs [listTheory.EVERY_EL])
  >> rw
       [compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_delta_product_outer_hessian_cv_def]
  >> irule
       (GEN_ALL
         compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_hessian_rel)
  >> rpt conj_tac
  >> fs
       [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def]
QED

Theorem bounded_case16594_object_delta_product_outer_hessian_runtime_semantic_rel:
  coordinate < 6 /\
  LENGTH center_boxes = 6 /\
  LENGTH outer_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  EVERY bounded_packed_q_interval_valid_cv outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_delta_gradient_cv
      center_boxes) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_delta_hessian_six_cv
      (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
      (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) ==>
  LIST_REL bounded_object_q_interval_cv_equiv
    (bounded_case16594_object_delta_product_outer_hessian_cv
      runtime_radii center_boxes outer_boxes coordinate)
    (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate)
Proof
  strip_tac
  >> irule
       compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_rel_trans
  >> qexists_tac
       `bounded_case16594_object_delta_product_outer_hessian_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          center_boxes outer_boxes coordinate`
  >> conj_tac
  >- (irule
        bounded_case16594_object_delta_product_outer_hessian_runtime_word_rel
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_outer_hessian_rel
  >> simp []
QED

Theorem bounded_case16594_object_delta_product_runtime_radii_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes coordinate /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii)
  ==>
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_delta_product_source_state_cv
      runtime_radii center_boxes outer_boxes coordinate)
    (bounded_object_q_taylor_complete_cv semantic_radii weights T
      (bounded_case16594_object_delta_product_center_value_cv
        center_boxes coordinate)
      (bounded_case16594_object_delta_product_center_gradient_cv
        center_boxes coordinate)
      (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
        semantic_radii center_boxes outer_boxes coordinate))
Proof
  rw
    [compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_product_refinement_context_def,
     compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
     compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_source_state_cv_def,
     compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def,
     LET_THM]
  >> BETA_TAC
  >- (irule
        (SIMP_RULE std_ss []
          (Q.SPEC `T`
            compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv))
      >> simp []
      >> rpt conj_tac
      >- (irule
            compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
          >> metis_tac
               [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded])
      >- (irule
            compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
          >> simp [])
      >- (irule
            bounded_case16594_object_delta_product_outer_hessian_runtime_semantic_rel
          >> simp []))
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_recomplete_semantic_valid
  >> simp []
  >> metis_tac
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
QED

Theorem bounded_case16594_object_delta_product_runtime_radii_eval_above_refines:
  bounded_case16594_object_delta_product_refinement_context
      semantic_radii weights center_boxes outer_boxes coordinate /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii)
  ==>
  ?object_result.
    bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
      outer_boxes coordinate = SOME object_result /\
    bounded_case16594_object_expression_eval_above 524403
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num coordinate)])
      (bounded_case16594_object_delta_product_source_state_cv
        runtime_radii center_boxes outer_boxes coordinate) /\
    bounded_object_q_taylor_runtime_refines
      (bounded_case16594_object_delta_product_source_state_cv
        runtime_radii center_boxes outer_boxes coordinate)
      object_result
Proof
  rw
    [compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_product_refinement_context_def]
  >> qexists_tac
       `bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_product_center_value_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_center_gradient_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
            semantic_radii center_boxes outer_boxes coordinate)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_delta_product_semantic_environment
      >> simp [])
  >> conj_tac
  >- (rw
        [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_source_state_eval)
      >> simp
           [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded]
      >> metis_tac
           [LIST_REL_LENGTH,rich_listTheory.LENGTH_MAP,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths])
  >> irule bounded_case16594_object_delta_product_runtime_radii_refines
  >> simp
       [compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_product_refinement_context_def]
QED

Theorem bounded_case16594_object_delta_neg_runtime_radii_eval_above_refines:
  bounded_case16594_object_delta_neg_refinement_context
      semantic_radii weights center_boxes coordinate /\
  EVERY bounded_object_q_encoded runtime_radii /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii)
  ==>
  ?object_result.
    bounded_object_q_delta_neg_derivative_cv semantic_radii center_boxes
      coordinate = SOME object_result /\
    bounded_case16594_object_expression_eval_above 262500
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (Num coordinate)])
      (bounded_case16594_object_delta_neg_source_state_cv
        runtime_radii center_boxes coordinate) /\
    bounded_object_q_taylor_runtime_refines
      (bounded_case16594_object_delta_neg_source_state_cv
        runtime_radii center_boxes coordinate)
      object_result
Proof
  rw
    [compute_boundedCase16594ObjectSpecializedDispatchStepInvariantTheory.bounded_case16594_object_delta_neg_refinement_context_def]
  >> qexists_tac
       `bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_neg_center_value_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_center_gradient_environment_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_neg_hessian_six_list_cv
            coordinate)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaNegRefinementBridgeTheory.bounded_case16594_object_delta_neg_semantic_environment
      >> simp [])
  >> conj_tac
  >- (rw
        [compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_expression_eval_above_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_source_state_eval)
      >> simp
           [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded]
      >> metis_tac
           [LIST_REL_LENGTH,rich_listTheory.LENGTH_MAP,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths])
  >> rw
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_def,
        compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_source_state_cv_def,
        compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def,
        LET_THM]
  >> BETA_TAC
  >- (irule
        (SIMP_RULE std_ss []
          (Q.SPEC `T`
            compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv))
      >> simp []
      >> rpt conj_tac
      >- (irule
            compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
          >> metis_tac
               [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded])
      >- (irule
            compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
          >> simp [])
      >- (irule
            compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
          >> simp []))
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_recomplete_semantic_valid
  >> simp []
  >> metis_tac
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
QED

val _ = export_theory ();
