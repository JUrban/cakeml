(*****************************************************************************
 * Production-state refinement for arbitrary 4*x_i*delta inputs.
 *
 * The packed source completion and the object Taylor completion denote the
 * same rationals but need not use byte-identical cv representations.  This
 * theory therefore joins them through the established rational-equivalence
 * relation rather than asserting representation equality.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductRefinementBridge
Ancestors
  compute_boundedCase16594ObjectDeltaProductSourceCompleteEval
  compute_boundedCase16594ObjectDeltaProductSemanticBridge
  compute_boundedCase16594ObjectRecompleteRelation
  compute_boundedCase16594ObjectMulRelation
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_interval_scale4_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv value value' ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_scale4_cv value)
    (bounded_object_q_interval_scale4_cv value')
Proof
  rw
    [compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_scale4_cv_def]
  >> metis_tac
       [compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong]
QED

Theorem bounded_case16594_object_delta_product_hessian_entry_rel:
  bounded_object_q_interval_cv_equiv runtime_box semantic_box /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_gradient semantic_gradient /\
  row < LENGTH runtime_gradient /\
  column < LENGTH runtime_gradient /\
  bounded_object_q_interval_cv_equiv runtime_entry semantic_entry ==>
  bounded_object_q_interval_cv_equiv
    (bounded_case16594_object_delta_product_hessian_entry_cv coordinate
      runtime_box runtime_gradient row column runtime_entry)
    (bounded_case16594_object_delta_product_hessian_entry_cv coordinate
      semantic_box semantic_gradient row column semantic_entry)
Proof
  strip_tac
  >> `LENGTH semantic_gradient = LENGTH runtime_gradient` by
       metis_tac [LIST_REL_LENGTH]
  >> `bounded_object_q_interval_cv_equiv
        (EL row runtime_gradient) (EL row semantic_gradient) /\
      bounded_object_q_interval_cv_equiv
        (EL column runtime_gradient) (EL column semantic_gradient)` by
       fs [LIST_REL_EL_EQN]
  >> rw
       [compute_boundedCase16594ObjectDeltaProductHessianEntryEvalTheory.bounded_case16594_object_delta_product_hessian_entry_cv_def]
  >> every_case_tac
  >> fs []
  >> metis_tac
       [bounded_case16594_object_interval_scale4_cv_equiv_cong,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong]
QED

Theorem bounded_case16594_object_delta_product_hessian_rel:
  !indices runtime_entries semantic_entries.
    bounded_object_q_interval_cv_equiv runtime_box semantic_box /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_gradient semantic_gradient /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_entries semantic_entries /\
    EVERY
      (\index.
        FST index < LENGTH runtime_gradient /\
        SND index < LENGTH runtime_gradient) indices ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (bounded_case16594_object_delta_product_hessian_cv coordinate
        runtime_box runtime_gradient indices runtime_entries)
      (bounded_case16594_object_delta_product_hessian_cv coordinate
        semantic_box semantic_gradient indices semantic_entries)
Proof
  Induct
  >- (rpt gen_tac
      >> Cases_on `runtime_entries`
      >> Cases_on `semantic_entries`
      >> simp
           [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def,
            LIST_REL_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `runtime_entries`
  >> Cases_on `semantic_entries`
  >> simp
       [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def,
        LIST_REL_def]
  >> strip_tac
  >> irule bounded_case16594_object_delta_product_hessian_entry_rel
  >> simp []
QED

Definition bounded_case16594_object_delta_product_semantic_outer_hessian_cv_def:
  bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate =
    let delta_hessian =
      bounded_object_q_delta_hessian_six_cv
        (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
        (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes);
        center_delta_gradient =
      bounded_case16594_object_delta_gradient_six_cv
        (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
        (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes);
        delta_gradient =
      bounded_object_q_taylor_gradient_complete_cv semantic_radii
        center_delta_gradient delta_hessian
    in
      bounded_case16594_object_delta_product_hessian_cv coordinate
        (EL coordinate outer_boxes) delta_gradient
        bounded_case16594_object_delta_product_indices6 delta_hessian
End

Theorem bounded_case16594_object_delta_product_semantic_outer_hessian_success:
  coordinate < 6 ==>
  bounded_object_q_delta_product_hessian_cv coordinate
      (EL coordinate outer_boxes)
      (bounded_object_q_taylor_gradient_complete_cv semantic_radii
        (bounded_case16594_object_delta_product_center_delta_gradient_cv
          center_boxes)
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
          (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)))
      bounded_delta64_hessian_indices
      (bounded_object_q_delta_hessian_six_cv
        (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
        (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) =
    SOME
      (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
        semantic_radii center_boxes outer_boxes coordinate)
Proof
  strip_tac
  >> `LENGTH
        (bounded_case16594_object_delta_product_center_delta_gradient_cv
          center_boxes) = 6` by
       simp
         [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length]
  >> `LENGTH
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
          (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) = 21` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> `LENGTH
        (bounded_object_q_taylor_gradient_complete_cv semantic_radii
          (bounded_case16594_object_delta_product_center_delta_gradient_cv
            center_boxes)
          (bounded_object_q_delta_hessian_six_cv
            (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
            (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes))) = 6` by
       (irule
          compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_taylor_gradient_complete_cv_length6
        >> simp [])
  >> rw
       [bounded_case16594_object_delta_product_semantic_outer_hessian_cv_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
        compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def,
        compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def]
  >> irule
       (GEN_ALL
         compute_boundedCase16594ObjectDeltaProductSemanticBridgeTheory.bounded_case16594_object_delta_product_hessian_semantic)
  >> simp
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length,
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_taylor_gradient_complete_cv_length6]
QED

Theorem bounded_case16594_object_delta_product_outer_hessian_rel:
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
      (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) ==>
  LIST_REL bounded_object_q_interval_cv_equiv
    (bounded_case16594_object_delta_product_outer_hessian_cv
      (MAP bounded_word64_object_q_cv semantic_radii)
      center_boxes outer_boxes coordinate)
    (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate)
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
          (MAP bounded_word64_object_q_cv semantic_radii)
          center_delta_gradient delta_hessian`
  >> qabbrev_tac
       `semantic_gradient = bounded_object_q_taylor_gradient_complete_cv
          semantic_radii center_delta_gradient delta_hessian`
  >> `LENGTH semantic_radii = 6` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
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
        runtime_gradient semantic_gradient` by
       (qunabbrev_tac `runtime_gradient`
        >> qunabbrev_tac `semantic_gradient`
        >> irule
             compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_source_gradient_complete6_word_semantic_rel
        >> simp [])
  >> `LENGTH runtime_gradient = 6` by
       (qunabbrev_tac `semantic_gradient`
        >> metis_tac
             [LIST_REL_LENGTH,
              compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_taylor_gradient_complete_cv_length6])
  >> `bounded_object_q_interval_cv_equiv
        (EL coordinate outer_boxes) (EL coordinate outer_boxes)` by
       (irule
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
        >> irule
             compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded
        >> fs [listTheory.EVERY_EL])
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        delta_hessian delta_hessian` by
       (irule
          compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
        >> simp [])
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_case16594_object_delta_product_hessian_cv coordinate
          (EL coordinate outer_boxes) runtime_gradient
          bounded_case16594_object_delta_product_indices6 delta_hessian)
        (bounded_case16594_object_delta_product_hessian_cv coordinate
          (EL coordinate outer_boxes) semantic_gradient
          bounded_case16594_object_delta_product_indices6 delta_hessian)` by
       (irule (GEN_ALL bounded_case16594_object_delta_product_hessian_rel)
        >> simp
             [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def])
  >> qunabbrev_tac `runtime_gradient`
  >> qunabbrev_tac `semantic_gradient`
  >> qunabbrev_tac `center_delta_gradient`
  >> qunabbrev_tac `delta_hessian`
  >> fs
       [compute_boundedCase16594ObjectDeltaProductOuterHessianEvalTheory.bounded_case16594_object_delta_product_outer_hessian_cv_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
        bounded_case16594_object_delta_product_semantic_outer_hessian_cv_def]
QED

Theorem bounded_case16594_object_q_cv_list_injective:
  !left right.
    bounded_object_q_cv_list left = bounded_object_q_cv_list right ==>
    left = right
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> metis_tac []
QED

Theorem bounded_case16594_object_delta_product_center_gradient_semantic:
  coordinate < 6 /\ LENGTH center_boxes = 6 ==>
  bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate =
    bounded_object_q_interval_list_scale4_cv
      (bounded_object_q_interval_list_add_at_cv
        (bounded_case16594_object_delta_product_center_delta_value_cv
          center_boxes)
        coordinate
        (bounded_object_q_interval_list_scale_cv
          (bounded_case16594_object_delta_product_center_coordinate_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_center_delta_gradient_cv
            center_boxes)))
Proof
  strip_tac
  >> irule bounded_case16594_object_q_cv_list_injective
  >> PURE_REWRITE_TAC
       [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_gradient_cv_def,
        GSYM
          compute_boundedCase16594ObjectDeltaProductGradientSixEvalTheory.bounded_case16594_object_delta_product_center_gradient_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectDeltaProductSemanticBridgeTheory.bounded_case16594_object_delta_product_gradient_six_semantic
  >> simp
       [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length]
QED

Theorem bounded_case16594_object_delta_product_semantic_environment:
  coordinate < 6 /\
  LENGTH center_boxes = 6 /\
  LENGTH outer_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights ==>
  bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
      outer_boxes coordinate =
    SOME
      (bounded_object_q_taylor_complete_cv semantic_radii weights T
        (bounded_case16594_object_delta_product_center_value_cv
          center_boxes coordinate)
        (bounded_case16594_object_delta_product_center_gradient_cv
          center_boxes coordinate)
        (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
          semantic_radii center_boxes outer_boxes coordinate))
Proof
  strip_tac
  >> `bounded_object_q_delta_product_hessian_cv coordinate
        (EL coordinate outer_boxes)
        (bounded_object_q_taylor_gradient_complete_cv semantic_radii
          (bounded_case16594_object_delta_gradient_six_cv
            (EL 0 center_boxes) (EL 1 center_boxes) (EL 2 center_boxes)
            (EL 3 center_boxes) (EL 4 center_boxes) (EL 5 center_boxes))
          (bounded_object_q_delta_hessian_six_cv
            (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
            (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)))
        bounded_delta64_hessian_indices
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
          (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) =
      SOME
        (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
          semantic_radii center_boxes outer_boxes coordinate)` by
       (irule
          (SIMP_RULE std_ss
            [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def]
            bounded_case16594_object_delta_product_semantic_outer_hessian_success)
        >> simp [])
  >> Cases_on `center_boxes` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `outer_boxes` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> rw
       [compute_boundedAnalyticObjectDeltaFourCoordinateRefinementTheory.bounded_object_q_delta_four_coordinate_cv_def,
        compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_value_cv_def,
        compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_pair_products_cv_def,
        compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_hessian_cv_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_value_cv_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_delta_gradient_cv_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_coordinate_cv_def,
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_center_value_cv_def,
        bounded_case16594_object_delta_product_center_gradient_semantic,
        compute_boundedCase16594ObjectDeltaProductSemanticBridgeTheory.bounded_case16594_object_delta_product_gradient_six_semantic,
        compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_semantic,
        compute_boundedCase16594ObjectDeltaProductSemanticBridgeTheory.bounded_case16594_object_nth_el_delta_product]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_word_radius_list_rel_refl:
  !semantic_radii.
    LIST_REL bounded_case10173_q_cv_equiv
      (MAP bounded_word64_object_q_cv semantic_radii)
      (MAP bounded_word64_object_q_cv semantic_radii)
Proof
  Induct
  >> simp
       [LIST_REL_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_decodes]
QED

Theorem bounded_case16594_object_delta_product_source_state_semantic:
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
  bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_value_cv
      center_boxes coordinate) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate) = 6 /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate) = 21 ==>
  ?object_result.
    bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
      outer_boxes coordinate = SOME object_result /\
    bounded_object_q_taylor_runtime_equiv
      (bounded_case16594_object_delta_product_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes outer_boxes coordinate)
      object_result
Proof
  strip_tac
  >> qexists_tac
       `bounded_object_q_taylor_complete_cv semantic_radii weights T
          (bounded_case16594_object_delta_product_center_value_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_center_gradient_cv
            center_boxes coordinate)
          (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
            semantic_radii center_boxes outer_boxes coordinate)`
  >> conj_tac
  >- (irule bounded_case16594_object_delta_product_semantic_environment
      >> simp [])
  >> PURE_REWRITE_TAC
       [compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_source_state_cv_def,
        LET_THM]
  >> BETA_TAC
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_taylor_complete_cv_def]
  >> irule
       (SIMP_RULE std_ss []
         (Q.SPEC `T`
           compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv))
  >> simp [bounded_case16594_object_word_radius_list_rel_refl]
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl
      >> metis_tac
           [compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_cv_object_encoded])
  >- (irule
        compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_packed_q_interval_valid_list_rel_refl
      >> simp [])
  >- (irule bounded_case16594_object_delta_product_outer_hessian_rel
      >> simp [])
QED

Theorem bounded_case16594_object_delta_product_source_state_eval_semantic:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_valid_cv center_boxes /\
  LENGTH center_boxes = 6 /\
  EVERY bounded_packed_q_interval_valid_cv outer_boxes /\
  LENGTH outer_boxes = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_delta_gradient_cv
      center_boxes) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_delta_hessian_six_cv
      (EL 0 outer_boxes) (EL 1 outer_boxes) (EL 2 outer_boxes)
      (EL 3 outer_boxes) (EL 4 outer_boxes) (EL 5 outer_boxes)) /\
  bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_value_cv
      center_boxes coordinate) /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_product_center_gradient_cv
      center_boxes coordinate) = 6 /\
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate) /\
  LENGTH
    (bounded_case16594_object_delta_product_semantic_outer_hessian_cv
      semantic_radii center_boxes outer_boxes coordinate) = 21 /\
  524403 < clock ==>
  ?object_result.
    bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
      outer_boxes coordinate = SOME object_result /\
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv
          (bounded_object_q_cv_list
            (MAP bounded_word64_object_q_cv semantic_radii));
         from_cv (bounded_object_q_cv_list center_boxes);
         from_cv (bounded_object_q_cv_list outer_boxes);
         from_cv (Num coordinate)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (bounded_case16594_object_delta_product_source_state_cv
            (MAP bounded_word64_object_q_cv semantic_radii)
            center_boxes outer_boxes coordinate)),refs) /\
    bounded_object_q_taylor_runtime_equiv
      (bounded_case16594_object_delta_product_source_state_cv
        (MAP bounded_word64_object_q_cv semantic_radii)
        center_boxes outer_boxes coordinate)
      object_result
Proof
  strip_tac
  >> `?object_result.
        bounded_object_q_delta_four_coordinate_cv semantic_radii center_boxes
          outer_boxes coordinate = SOME object_result /\
        bounded_object_q_taylor_runtime_equiv
          (bounded_case16594_object_delta_product_source_state_cv
            (MAP bounded_word64_object_q_cv semantic_radii)
            center_boxes outer_boxes coordinate)
          object_result` by
       (irule bounded_case16594_object_delta_product_source_state_semantic
        >> simp [])
  >> qexists_tac `object_result`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaProductSourceCompleteEvalTheory.bounded_case16594_object_delta_product_source_state_eval
      >> simp
           [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_list_encoded,
            listTheory.EVERY_MAP,
            compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
      >> metis_tac
           [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
