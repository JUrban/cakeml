(*****************************************************************************
 * Semantic join for the arbitrary-input -d(delta)/dx_i production state.
 *
 * This theory identifies the exact components returned by the production
 * evaluator with the object-q construction used by the generic analytic
 * refinement.  It deliberately precedes the genuine-cell/program join: all
 * identities below are symbolic in the six center intervals and coordinate.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaNegSemanticBridge
Ancestors
  compute_boundedCase16594ObjectDeltaNegCompleteEval
  compute_boundedAnalyticObjectDeltaNegDerivativeRefinement
  compute_boundedCase16594ObjectRecompleteRelation
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_gradient_components_el:
  !coordinates products results index.
    bounded_object_q_delta_gradient_components_cv coordinates products =
      SOME results /\
    index < LENGTH coordinates ==>
    bounded_object_q_delta_gradient_component_from_products_cv
      (EL index coordinates) products = SOME (EL index results)
Proof
  Induct
  >> rpt gen_tac
  >> Cases_on `results`
  >> simp
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_components_cv_def]
  >> every_case_tac
  >> gvs []
  >> Cases_on `index`
  >> simp []
  >> metis_tac []
QED

Theorem bounded_case16594_object_delta_gradient_component_six_semantic:
  coordinate < 6 ==>
  bounded_object_q_delta_gradient_component_from_products_cv coordinate
      (bounded_object_q_delta_pair_products_six_cv x0 x1 x2 x3 x4 x5) =
    SOME
      (EL coordinate
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5))
Proof
  strip_tac
  >> `EL coordinate [0;1;2;3;4;5] = coordinate` by
       (`coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
         coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
          intLib.ARITH_TAC
        >> fs [])
  >> qspecl_then
       [`[0;1;2;3;4;5]`,
        `bounded_object_q_delta_pair_products_six_cv x0 x1 x2 x3 x4 x5`,
        `bounded_case16594_object_delta_gradient_six_cv x0 x1 x2 x3 x4 x5`,
        `coordinate`]
       mp_tac bounded_case16594_object_delta_gradient_components_el
  >> impl_tac
  >- (conj_tac
      >- ACCEPT_TAC
           (REWRITE_RULE
             [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_from_products_cv_def]
             compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_semantic)
      >> fs [])
  >> fs []
QED

Theorem bounded_case16594_object_delta_basis_six_semantic:
  coordinate < 6 ==>
  bounded_case16594_object_delta_basis_six_cv coordinate =
    bounded_object_q_unit_vector coordinate
Proof
  strip_tac
  >> `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
      coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
       intLib.ARITH_TAC
  >> fs
       [compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_basis_six_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_unit_vector_def,
        compute_boundedCase16594ObjectVariableEvalTheory.bounded_case16594_object_one_interval_cv_def,
        compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_zero_interval_identity]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_neg_semantic_trace_six:
  coordinate < 6 /\
  bounded_taylor_radius_pairs radii = SOME weights ==>
  bounded_object_q_delta_neg_derivative_cv radii
      [x0;x1;x2;x3;x4;x5] coordinate =
    SOME
      (bounded_object_q_taylor_complete_cv radii weights T
        (bounded_case16594_object_delta_neg_center_value_cv coordinate
          x0 x1 x2 x3 x4 x5)
        (bounded_case16594_object_delta_neg_center_gradient_list_cv coordinate
          x0 x1 x2 x3 x4 x5)
        (bounded_case16594_object_delta_neg_hessian_six_list_cv coordinate))
Proof
  strip_tac
  >> `bounded_object_q_delta_pair_products_cv [x0;x1;x2;x3;x4;x5] =
        SOME
          (bounded_object_q_delta_pair_products_six_cv
            x0 x1 x2 x3 x4 x5)` by
       simp
         [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_pair_products_cv_def]
  >> `bounded_object_q_delta_hessian_cv [x0;x1;x2;x3;x4;x5] =
        SOME (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5)` by
       simp
         [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_hessian_cv_def]
  >> `bounded_hessian64_rows
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) =
      SOME
        (bounded_packed_q_source_hessian6_rows
          (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5))` by
       (irule
          compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_exact
        >> simp
             [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length])
  >> `bounded_object_q_nth
        (bounded_packed_q_source_hessian6_rows
          (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5))
        coordinate =
      SOME
        (EL coordinate
          (bounded_packed_q_source_hessian6_rows
            (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5)))` by
       (irule
          compute_boundedCase16594ObjectDeltaProductSemanticBridgeTheory.bounded_case16594_object_nth_el_delta_product
        >> simp
             [compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_packed_q_source_hessian6_rows_def])
  >> `bounded_object_q_delta_hessian_cv
        (bounded_object_q_unit_vector coordinate) =
      SOME
        (bounded_object_q_delta_hessian_six_cv
          (EL 0 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 1 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 2 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 3 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 4 (bounded_case16594_object_delta_basis_six_cv coordinate))
          (EL 5 (bounded_case16594_object_delta_basis_six_cv coordinate)))` by
       (rw [GSYM bounded_case16594_object_delta_basis_six_semantic]
        >> simp
             [compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_object_q_delta_hessian_cv_def,
              compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_basis_six_cv_def])
  >> rw
       [compute_boundedAnalyticObjectDeltaNegDerivativeRefinementTheory.bounded_object_q_delta_neg_derivative_cv_def,
        bounded_case16594_object_delta_gradient_component_six_semantic,
        compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_value_cv_def,
        compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_center_gradient_list_cv_def,
        compute_boundedCase16594ObjectDeltaNegCompleteEvalTheory.bounded_case16594_object_delta_neg_hessian_six_list_cv_def]
QED

val _ = export_theory ();
