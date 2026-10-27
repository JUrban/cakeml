(*****************************************************************************
 * Exact object-q refinement for the complete optimized 4*x_i*delta state.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaFourCoordinateRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaNegDerivativeRefinement
Libs
  bossLib preamble

Definition bounded_object_q_delta_four_coordinate_cv_def:
  bounded_object_q_delta_four_coordinate_cv radii object_center_environment
      object_box_environment (coordinate:num) =
    case bounded_taylor_radius_pairs radii of
    | NONE => NONE
    | SOME weights =>
      case bounded_object_q_delta_value_cv object_center_environment of
      | NONE => NONE
      | SOME center_delta =>
        case bounded_object_q_delta_pair_products_cv
          object_center_environment of
        | NONE => NONE
        | SOME center_products =>
          case bounded_object_q_delta_gradient_from_products_cv
            center_products of
          | NONE => NONE
          | SOME center_delta_gradient =>
            case bounded_object_q_delta_hessian_cv object_box_environment of
            | NONE => NONE
            | SOME box_delta_hessian =>
              let box_delta_gradient =
                    bounded_object_q_taylor_gradient_complete_cv radii
                      center_delta_gradient box_delta_hessian
              in
                case bounded_object_q_nth object_center_environment
                  coordinate of
                | NONE => NONE
                | SOME center_coordinate =>
                  case bounded_object_q_nth object_box_environment
                    coordinate of
                  | NONE => NONE
                  | SOME box_coordinate =>
                    let center_product =
                          bounded_object_q_interval_mul_cv
                            center_coordinate center_delta;
                        center_value =
                          bounded_object_q_interval_scale4_cv center_product;
                        center_gradient_base =
                          bounded_object_q_interval_list_scale_cv
                            center_coordinate center_delta_gradient;
                        center_gradient_unscaled =
                          bounded_object_q_interval_list_add_at_cv center_delta
                            coordinate center_gradient_base;
                        center_gradient =
                          bounded_object_q_interval_list_scale4_cv
                            center_gradient_unscaled
                    in
                      case bounded_object_q_delta_product_hessian_cv
                        coordinate box_coordinate box_delta_gradient
                        bounded_delta64_hessian_indices box_delta_hessian of
                      | NONE => NONE
                      | SOME result_hessian =>
                          SOME
                            (bounded_object_q_taylor_complete_cv radii weights T
                              center_value center_gradient result_hessian)
End

Theorem bounded_delta64_four_coordinate_trace:
  bounded_delta64_four_coordinate radii word_center_environment
      word_box_environment coordinate = SOME word_result ==>
  ?word_center_delta word_center_products word_center_delta_gradient
      word_box_delta_hessian word_box_delta_gradient word_center_coordinate
      word_box_coordinate word_center_product word_center_value
      word_center_gradient_base word_center_gradient_unscaled
      word_center_gradient word_result_hessian.
    bounded_delta64_value word_center_environment = SOME word_center_delta /\
    bounded_delta64_pair_products word_center_environment =
      SOME word_center_products /\
    bounded_delta64_gradient_from_products word_center_products =
      SOME word_center_delta_gradient /\
    bounded_delta64_hessian word_box_environment =
      SOME word_box_delta_hessian /\
    bounded_taylor_gradient_complete radii word_center_delta_gradient
      word_box_delta_hessian = SOME word_box_delta_gradient /\
    bounded_interval64_nth word_center_environment coordinate =
      SOME word_center_coordinate /\
    bounded_interval64_nth word_box_environment coordinate =
      SOME word_box_coordinate /\
    bounded_interval64_mul word_center_coordinate word_center_delta =
      SOME word_center_product /\
    bounded_interval64_scale4 word_center_product = SOME word_center_value /\
    bounded_interval64_list_scale word_center_coordinate
      word_center_delta_gradient = SOME word_center_gradient_base /\
    bounded_interval64_list_add_at word_center_delta coordinate
      word_center_gradient_base = SOME word_center_gradient_unscaled /\
    bounded_interval64_list_scale4 word_center_gradient_unscaled =
      SOME word_center_gradient /\
    bounded_delta64_product_hessian coordinate word_box_coordinate
      word_box_delta_gradient bounded_delta64_hessian_indices
      word_box_delta_hessian = SOME word_result_hessian /\
    bounded_taylor64_complete radii T word_center_value
      word_center_gradient word_result_hessian = SOME word_result
Proof
  strip_tac
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_four_coordinate_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_delta64_four_coordinate_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
    word_box_environment object_box_environment /\
  bounded_delta64_four_coordinate radii word_center_environment
    word_box_environment coordinate = SOME word_result ==>
  ?object_result.
    bounded_object_q_delta_four_coordinate_cv radii
      object_center_environment object_box_environment coordinate =
        SOME object_result /\
    bounded_taylor64_covers_object_q word_result object_result
Proof
  strip_tac
  >> drule bounded_delta64_four_coordinate_trace
  >> strip_tac
  >> drule_all
       compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_delta64_value_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_value_cv object_center_environment =
          SOME object_center_delta`
  >> drule_all
       compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_delta64_pair_products_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_pair_products_cv object_center_environment =
          SOME object_center_products`
  >> drule_all
       compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_delta64_gradient_from_products_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_gradient_from_products_cv
          object_center_products = SOME object_center_delta_gradient`
  >> drule_all
       (Q.INST
         [`word_environment` |-> `word_box_environment`,
          `object_environment` |-> `object_box_environment`,
          `word_result` |-> `word_box_delta_hessian`]
         compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_delta64_hessian_covers_object_q)
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_hessian_cv object_box_environment =
          SOME object_box_delta_hessian`
  >> drule_all
       (Q.SPECL
         [`word_box_delta_gradient`, `radii`, `object_box_delta_hessian`,
          `object_center_delta_gradient`, `word_box_delta_hessian`,
          `word_center_delta_gradient`]
         (GEN_ALL
           compute_boundedAnalyticObjectGradientRefinementTheory.bounded_taylor_gradient_complete_covers_object_q))
  >> strip_tac
  >> `?object_center_coordinate.
        bounded_object_q_nth object_center_environment coordinate =
          SOME object_center_coordinate /\
        bounded_interval64_covers_object_q word_center_coordinate
          object_center_coordinate` by
       (match_mp_tac
          (Q.SPECL
            [`word_center_environment`, `object_center_environment`,
             `coordinate`, `word_center_coordinate`]
            compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_nth_covers_object_q_nth)
        >> simp [])
  >> `?object_box_coordinate.
        bounded_object_q_nth object_box_environment coordinate =
          SOME object_box_coordinate /\
        bounded_interval64_covers_object_q word_box_coordinate
          object_box_coordinate` by
       (match_mp_tac
          (Q.SPECL
            [`word_box_environment`, `object_box_environment`,
             `coordinate`, `word_box_coordinate`]
            compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_nth_covers_object_q_nth)
        >> simp [])
  >> drule_all
       (Q.INST
         [`left` |-> `word_center_coordinate`,
          `left_object_interval` |-> `object_center_coordinate`,
          `right` |-> `word_center_delta`,
          `right_object_interval` |-> `object_center_delta`,
          `result` |-> `word_center_product`]
         compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q)
  >> strip_tac
  >> drule_all
       (Q.INST
         [`word_value` |-> `word_center_product`,
          `object_value` |->
            `bounded_object_q_interval_mul_cv object_center_coordinate
               object_center_delta`,
          `result` |-> `word_center_value`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_scale4_covers_object_q)
  >> strip_tac
  >> drule_all
       (Q.INST
         [`scalar` |-> `word_center_coordinate`,
          `object_scalar` |-> `object_center_coordinate`]
         (Q.SPECL
           [`word_center_delta_gradient`, `object_center_delta_gradient`,
            `word_center_gradient_base`]
           compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_interval64_list_scale_covers_object_q))
  >> strip_tac
  >> drule_all
       (Q.INST
         [`word_value` |-> `word_center_delta`,
          `object_value` |-> `object_center_delta`]
         (Q.SPECL
           [`coordinate`, `word_center_gradient_base`,
            `bounded_object_q_interval_list_scale_cv object_center_coordinate
               object_center_delta_gradient`,
            `word_center_gradient_unscaled`]
           compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_list_add_at_covers_object_q))
  >> strip_tac
  >> drule_all
       (Q.SPECL
         [`word_center_gradient_unscaled`,
          `bounded_object_q_interval_list_add_at_cv object_center_delta
             coordinate
             (bounded_object_q_interval_list_scale_cv
               object_center_coordinate object_center_delta_gradient)`,
          `word_center_gradient`]
         compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_interval64_list_scale4_covers_object_q)
  >> strip_tac
  >> `?object_result_hessian.
        bounded_object_q_delta_product_hessian_cv coordinate
          object_box_coordinate
          (bounded_object_q_taylor_gradient_complete_cv radii
            object_center_delta_gradient object_box_delta_hessian)
          bounded_delta64_hessian_indices object_box_delta_hessian =
            SOME object_result_hessian /\
        LIST_REL bounded_interval64_covers_object_q word_result_hessian
          object_result_hessian` by
       (irule
          (Q.SPECL
            [`word_box_delta_gradient`, `word_box_coordinate`,
             `bounded_object_q_taylor_gradient_complete_cv radii
                object_center_delta_gradient object_box_delta_hessian`,
             `object_box_coordinate`, `coordinate`,
             `bounded_delta64_hessian_indices`, `word_box_delta_hessian`,
             `object_box_delta_hessian`, `word_result_hessian`]
            (GEN_ALL
              compute_boundedAnalyticObjectDeltaProductHessianRefinementTheory.bounded_delta64_product_hessian_covers_object_q))
        >> qexists_tac `word_box_coordinate`
        >> qexists_tac `word_box_delta_gradient`
        >> qexists_tac `word_box_delta_hessian`
        >> simp [])
  >> drule
       compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_taylor64_complete_radius_pairs
  >> strip_tac
  >> rename1 `bounded_taylor_radius_pairs radii = SOME weights`
  >> qexists_tac
       `bounded_object_q_taylor_complete_cv radii weights T
          (bounded_object_q_interval_scale4_cv
            (bounded_object_q_interval_mul_cv object_center_coordinate
              object_center_delta))
          (bounded_object_q_interval_list_scale4_cv
            (bounded_object_q_interval_list_add_at_cv object_center_delta
              coordinate
              (bounded_object_q_interval_list_scale_cv
                object_center_coordinate object_center_delta_gradient)))
          object_result_hessian`
  >> conj_tac
  >- simp [bounded_object_q_delta_four_coordinate_cv_def]
  >> match_mp_tac
       (Q.SPECL
         [`word_result`, `word_result_hessian`, `word_center_gradient`,
          `word_center_value`, `weights`, `T`, `radii`,
          `object_result_hessian`,
          `bounded_object_q_interval_list_scale4_cv
             (bounded_object_q_interval_list_add_at_cv object_center_delta
               coordinate
               (bounded_object_q_interval_list_scale_cv
                 object_center_coordinate object_center_delta_gradient))`,
          `bounded_object_q_interval_scale4_cv
             (bounded_object_q_interval_mul_cv object_center_coordinate
               object_center_delta)`]
         (GEN_ALL
           compute_boundedAnalyticObjectDeltaStateSupportTheory.bounded_taylor64_complete_refines_object_q_taylor))
  >> simp []
QED

val _ = export_theory ();
