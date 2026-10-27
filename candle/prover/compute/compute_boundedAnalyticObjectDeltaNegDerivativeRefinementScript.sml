(*****************************************************************************
 * Exact object-q refinement for the complete optimized -d(delta)/dx_i state.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaNegDerivativeRefinement
Ancestors
  compute_boundedAnalyticObjectDeltaStateSupport
Libs
  bossLib preamble

Definition bounded_object_q_delta_neg_derivative_cv_def:
  bounded_object_q_delta_neg_derivative_cv radii object_environment
      (coordinate:num) =
    case bounded_taylor_radius_pairs radii of
    | NONE => NONE
    | SOME weights =>
      case bounded_object_q_delta_pair_products_cv object_environment of
      | NONE => NONE
      | SOME products =>
        case bounded_object_q_delta_gradient_component_from_products_cv
          coordinate products of
        | NONE => NONE
        | SOME center_value =>
          case bounded_object_q_delta_hessian_cv object_environment of
          | NONE => NONE
          | SOME center_hessian =>
            case bounded_hessian64_rows center_hessian of
            | NONE => NONE
            | SOME center_rows =>
              case bounded_object_q_nth center_rows coordinate of
              | NONE => NONE
              | SOME center_gradient =>
                case bounded_object_q_delta_hessian_cv
                  (bounded_object_q_unit_vector coordinate) of
                | NONE => NONE
                | SOME result_hessian =>
                  SOME
                    (bounded_object_q_taylor_complete_cv radii weights T
                      (bounded_object_q_interval_neg_cv center_value)
                      (MAP bounded_object_q_interval_neg_cv center_gradient)
                      (MAP bounded_object_q_interval_neg_cv result_hessian))
End

Theorem bounded_delta64_neg_derivative_trace:
  bounded_delta64_neg_derivative radii word_environment coordinate =
      SOME word_result ==>
  ?word_products word_center_value word_center_hessian word_center_rows
      word_center_gradient word_basis word_result_hessian.
    bounded_delta64_pair_products word_environment = SOME word_products /\
    bounded_delta64_gradient_component_from_products coordinate
      word_products = SOME word_center_value /\
    bounded_delta64_hessian word_environment = SOME word_center_hessian /\
    bounded_hessian64_rows word_center_hessian = SOME word_center_rows /\
    bounded_interval64_nth word_center_rows coordinate =
      SOME word_center_gradient /\
    bounded_interval64_unit_vector coordinate = SOME word_basis /\
    bounded_delta64_hessian word_basis = SOME word_result_hessian /\
    bounded_taylor64_complete radii T
      (bounded_interval64_neg word_center_value)
      (bounded_interval64_list_neg word_center_gradient)
      (bounded_interval64_list_neg word_result_hessian) = SOME word_result
Proof
  strip_tac
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_neg_derivative_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_delta64_neg_derivative_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_environment object_environment /\
  bounded_delta64_neg_derivative radii word_environment coordinate =
    SOME word_result ==>
  ?object_result.
    bounded_object_q_delta_neg_derivative_cv radii object_environment
      coordinate = SOME object_result /\
    bounded_taylor64_covers_object_q word_result object_result
Proof
  strip_tac
  >> drule bounded_delta64_neg_derivative_trace
  >> strip_tac
  >> drule_all bounded_delta64_pair_products_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_pair_products_cv object_environment =
          SOME object_products`
  >> drule_all
       compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_delta64_gradient_component_from_products_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_gradient_component_from_products_cv
          coordinate object_products = SOME object_center_value`
  >> drule_all bounded_delta64_hessian_covers_object_q
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_hessian_cv object_environment =
          SOME object_center_hessian`
  >> drule_all
       compute_boundedAnalyticObjectGradientRefinementTheory.bounded_hessian64_rows_list_rel_right
  >> strip_tac
  >> rename1
       `bounded_hessian64_rows object_center_hessian =
          SOME object_center_rows`
  >> drule_all bounded_nth_list_rel
  >> strip_tac
  >> rename1
       `bounded_object_q_nth object_center_rows coordinate =
          SOME object_center_gradient`
  >> imp_res_tac
       compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_unit_vector_covers_object_q
  >> drule_all
       (Q.INST
         [`word_environment` |-> `word_basis`,
          `object_environment` |-> `bounded_object_q_unit_vector coordinate`,
          `word_result` |-> `word_result_hessian`]
         bounded_delta64_hessian_covers_object_q)
  >> strip_tac
  >> rename1
       `bounded_object_q_delta_hessian_cv
          (bounded_object_q_unit_vector coordinate) =
          SOME object_result_hessian`
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q
  >> `LIST_REL bounded_interval64_covers_object_q
        (bounded_interval64_list_neg word_center_gradient)
        (MAP bounded_object_q_interval_neg_cv object_center_gradient)` by
       (match_mp_tac
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_list_neg_covers_object_q
        >> simp [])
  >> `LIST_REL bounded_interval64_covers_object_q
        (bounded_interval64_list_neg word_result_hessian)
        (MAP bounded_object_q_interval_neg_cv object_result_hessian)` by
       (match_mp_tac
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_list_neg_covers_object_q
        >> simp [])
  >> drule bounded_taylor64_complete_radius_pairs
  >> strip_tac
  >> rename1 `bounded_taylor_radius_pairs radii = SOME weights`
  >> qexists_tac
       `bounded_object_q_taylor_complete_cv radii weights T
          (bounded_object_q_interval_neg_cv object_center_value)
          (MAP bounded_object_q_interval_neg_cv object_center_gradient)
          (MAP bounded_object_q_interval_neg_cv object_result_hessian)`
  >> conj_tac
  >- simp [bounded_object_q_delta_neg_derivative_cv_def]
  >> match_mp_tac
       (Q.INST
         [`word_center` |-> `bounded_interval64_neg word_center_value`,
          `object_center` |->
            `bounded_object_q_interval_neg_cv object_center_value`,
          `word_center_gradient` |->
            `bounded_interval64_list_neg word_center_gradient`,
          `object_center_gradient` |->
            `MAP bounded_object_q_interval_neg_cv object_center_gradient`,
          `word_hessian` |->
            `bounded_interval64_list_neg word_result_hessian`,
          `object_hessian` |->
            `MAP bounded_object_q_interval_neg_cv object_result_hessian`,
          `result_domain` |-> `T`, `word_result` |-> `word_result`,
          `radii` |-> `radii`, `weights` |-> `weights`]
         bounded_taylor64_complete_refines_object_q_taylor)
  >> simp []
QED

val _ = export_theory ();
