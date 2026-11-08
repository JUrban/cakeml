(*****************************************************************************
 * Semantic identities for the complete exact jet of 4*x_i*delta.
 *
 * These lemmas identify the production evaluator results for the packed
 * gradient and Hessian with the object-q constructors used by the universal
 * analytic refinement.  They contain no captured case-16594 arithmetic.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductSemanticBridge
Ancestors
  compute_boundedCase16594ObjectDeltaProductHessianCompleteEval
  compute_boundedAnalyticObjectDeltaFourCoordinateRefinement
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_nth_el_delta_product:
  !items index.
    index < LENGTH items ==>
    bounded_object_q_nth items index = SOME (EL index items)
Proof
  Induct_on `items`
  >> Cases_on `index`
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_nth_def]
QED

Theorem bounded_case16594_object_delta_select_signed_terms_success:
  !indices products.
    EVERY (\index. SND index < LENGTH products) indices ==>
    ?terms.
      bounded_object_q_delta_select_signed_terms_cv indices products =
        SOME terms
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_select_signed_terms_cv_def]
  >> gen_tac
  >> PairCases_on `h`
  >> simp []
  >> rpt strip_tac
  >> `bounded_object_q_nth products h1 = SOME (EL h1 products)` by
       simp [bounded_case16594_object_nth_el_delta_product]
  >> qpat_x_assum `!products. _` (qspec_then `products` mp_tac)
  >> simp []
  >> strip_tac
  >> qexists_tac `(h0,EL h1 products)::terms`
  >> simp
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_select_signed_terms_cv_def]
QED

Theorem bounded_case16594_object_delta_gradient_signed_terms_success:
  coordinate < 6 /\ 21 <= LENGTH products ==>
  ?terms.
    bounded_object_q_delta_gradient_signed_terms_cv coordinate products =
      SOME terms
Proof
  strip_tac
  >> `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
      coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
       intLib.ARITH_TAC
  >> fs
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_signed_terms_cv_def,
        compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_delta_gradient_signed_indices_def]
  >- (irule bounded_case16594_object_delta_select_signed_terms_success
      >> simp [] >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_delta_select_signed_terms_success
      >> simp [] >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_delta_select_signed_terms_success
      >> simp [] >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_delta_select_signed_terms_success
      >> simp [] >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_delta_select_signed_terms_success
      >> simp [] >> intLib.ARITH_TAC)
  >- (irule bounded_case16594_object_delta_select_signed_terms_success
      >> simp [] >> intLib.ARITH_TAC)
QED

Theorem bounded_case16594_object_delta_gradient_component_success:
  coordinate < 6 /\ 21 <= LENGTH products ==>
  ?result.
    bounded_object_q_delta_gradient_component_from_products_cv
      coordinate products = SOME result
Proof
  strip_tac
  >> drule_all
       bounded_case16594_object_delta_gradient_signed_terms_success
  >> strip_tac
  >> qexists_tac
       `bounded_object_q_interval_sum_cv
          (bounded_object_q_delta_apply_signed_terms_cv terms)`
  >> simp
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_component_from_products_cv_def]
QED

Theorem bounded_case16594_object_delta_gradient_components_success:
  !coordinates products.
    EVERY (\coordinate. coordinate < 6) coordinates /\
    21 <= LENGTH products ==>
    ?results.
      bounded_object_q_delta_gradient_components_cv coordinates products =
        SOME results
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_components_cv_def]
  >> rpt gen_tac
  >> strip_tac
  >> fs []
  >> drule_all bounded_case16594_object_delta_gradient_component_success
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> qexists_tac `result::results`
  >> simp
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_components_cv_def]
QED

Theorem bounded_case16594_object_delta_gradient_components_length:
  !coordinates products results.
    bounded_object_q_delta_gradient_components_cv coordinates products =
      SOME results ==>
    LENGTH results = LENGTH coordinates
Proof
  Induct
  >> rpt gen_tac
  >> rw
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_components_cv_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_case16594_object_delta_gradient_from_products_success:
  21 <= LENGTH products ==>
  ?result.
    bounded_object_q_delta_gradient_from_products_cv products = SOME result
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_from_products_cv_def]
  >> irule bounded_case16594_object_delta_gradient_components_success
  >> simp []
QED

Theorem bounded_case16594_object_delta_gradient_from_products_length:
  bounded_object_q_delta_gradient_from_products_cv products = SOME result ==>
  LENGTH result = 6
Proof
  strip_tac
  >> `bounded_object_q_delta_gradient_components_cv [0;1;2;3;4;5]
        products = SOME result` by
       fs
         [compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_from_products_cv_def]
  >> drule bounded_case16594_object_delta_gradient_components_length
  >> simp []
QED

Theorem bounded_case16594_object_delta_product_hessian_entry_semantic:
  row < LENGTH delta_gradient /\ column < LENGTH delta_gradient ==>
  bounded_object_q_delta_product_hessian_entry_cv coordinate box_coordinate
      delta_gradient row column delta_hessian =
    SOME
      (bounded_case16594_object_delta_product_hessian_entry_cv coordinate
        box_coordinate delta_gradient row column delta_hessian)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectDeltaProductHessianRefinementTheory.bounded_object_q_delta_product_hessian_entry_cv_def,
        compute_boundedCase16594ObjectDeltaProductHessianEntryEvalTheory.bounded_case16594_object_delta_product_hessian_entry_cv_def]
  >> simp [bounded_case16594_object_nth_el_delta_product]
QED

Theorem bounded_case16594_object_delta_product_hessian_semantic:
  !(indices:(num # num) list) (entries:cv list).
    EVERY
      (\index.
        FST index < LENGTH delta_gradient /\
        SND index < LENGTH delta_gradient) indices /\
    LENGTH indices = LENGTH entries ==>
    bounded_object_q_delta_product_hessian_cv coordinate box_coordinate
        delta_gradient indices entries =
      SOME
        (bounded_case16594_object_delta_product_hessian_cv coordinate
          box_coordinate delta_gradient indices entries)
Proof
  Induct_on `indices`
  >- (Cases_on `entries`
      >> simp
           [compute_boundedAnalyticObjectDeltaProductHessianRefinementTheory.bounded_object_q_delta_product_hessian_cv_def,
            compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def])
  >> Cases_on `h`
  >> Cases_on `entries`
  >> simp
       [compute_boundedAnalyticObjectDeltaProductHessianRefinementTheory.bounded_object_q_delta_product_hessian_cv_def,
        compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def]
  >> strip_tac
  >> simp [bounded_case16594_object_delta_product_hessian_entry_semantic]
QED

Theorem bounded_case16594_object_delta_product_gradient_six_semantic:
  coordinate < 6 /\ LENGTH delta_gradient = 6 ==>
  bounded_case16594_object_delta_product_center_gradient_six_cv coordinate
      coordinate_value delta_value delta_gradient =
    bounded_object_q_cv_list
      (bounded_object_q_interval_list_scale4_cv
        (bounded_object_q_interval_list_add_at_cv delta_value coordinate
          (bounded_object_q_interval_list_scale_cv coordinate_value
            delta_gradient)))
Proof
  strip_tac
  >> Cases_on `delta_gradient` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> Cases_on `t` >> fs []
  >> Cases_on `t'` >> fs []
  >> `coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
      coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
       intLib.ARITH_TAC
  >> fs []
  >> simp
       [compute_boundedCase16594ObjectDeltaProductGradientSixEvalTheory.bounded_case16594_object_delta_product_center_gradient_six_cv_def,
        compute_boundedCase16594ObjectDeltaProductGradientEntryEvalTheory.bounded_case16594_object_delta_product_center_gradient_entry_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def,
        compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_list_add_at_cv_def,
        compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_list_scale4_cv_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
