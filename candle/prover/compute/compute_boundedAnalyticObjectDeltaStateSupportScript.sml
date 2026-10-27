(*****************************************************************************
 * Shared object-q packaging for the two complete compact delta states.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectDeltaStateSupport
Ancestors
  compute_boundedAnalyticObjectDeltaProductHessianRefinement
Libs
  bossLib preamble

Definition bounded_object_q_delta_pair_products_cv_def:
  bounded_object_q_delta_pair_products_cv environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
        SOME
          (bounded_object_q_delta_pair_products_six_cv
            x0 x1 x2 x3 x4 x5)
    | _ => NONE
End

Theorem bounded_delta64_pair_products_six_shape:
  bounded_delta64_pair_products environment = SOME result ==>
  ?x0 x1 x2 x3 x4 x5.
    environment = [x0;x1;x2;x3;x4;x5]
Proof
  strip_tac
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_pair_products_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_delta64_pair_products_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_environment object_environment /\
  bounded_delta64_pair_products word_environment = SOME word_result ==>
  ?object_result.
    bounded_object_q_delta_pair_products_cv object_environment =
      SOME object_result /\
    LIST_REL bounded_interval64_covers_object_q word_result object_result
Proof
  strip_tac
  >> drule bounded_delta64_pair_products_six_shape
  >> strip_tac
  >> rename1 `word_environment = [word0;word1;word2;word3;word4;word5]`
  >> gvs []
  >> rename1 `bounded_interval64_covers_object_q word0 object0`
  >> rename1 `bounded_interval64_covers_object_q word1 object1`
  >> rename1 `bounded_interval64_covers_object_q word2 object2`
  >> rename1 `bounded_interval64_covers_object_q word3 object3`
  >> rename1 `bounded_interval64_covers_object_q word4 object4`
  >> rename1 `bounded_interval64_covers_object_q word5 object5`
  >> qexists_tac
       `bounded_object_q_delta_pair_products_six_cv
          object0 object1 object2 object3 object4 object5`
  >> simp [bounded_object_q_delta_pair_products_cv_def]
  >> metis_tac
       [compute_boundedAnalyticObjectDeltaProductRefinementTheory.bounded_delta64_pair_products_six_covers_object_q]
QED

Definition bounded_object_q_delta_hessian_cv_def:
  bounded_object_q_delta_hessian_cv environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
        SOME (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5)
    | _ => NONE
End

Theorem bounded_delta64_hessian_six_shape:
  bounded_delta64_hessian environment = SOME result ==>
  ?x0 x1 x2 x3 x4 x5.
    environment = [x0;x1;x2;x3;x4;x5]
Proof
  strip_tac
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_delta64_hessian_covers_object_q:
  LIST_REL bounded_interval64_covers_object_q
    word_environment object_environment /\
  bounded_delta64_hessian word_environment = SOME word_result ==>
  ?object_result.
    bounded_object_q_delta_hessian_cv object_environment =
      SOME object_result /\
    LIST_REL bounded_interval64_covers_object_q word_result object_result
Proof
  strip_tac
  >> drule bounded_delta64_hessian_six_shape
  >> strip_tac
  >> rename1 `word_environment = [word0;word1;word2;word3;word4;word5]`
  >> gvs []
  >> rename1 `bounded_interval64_covers_object_q word0 object0`
  >> rename1 `bounded_interval64_covers_object_q word1 object1`
  >> rename1 `bounded_interval64_covers_object_q word2 object2`
  >> rename1 `bounded_interval64_covers_object_q word3 object3`
  >> rename1 `bounded_interval64_covers_object_q word4 object4`
  >> rename1 `bounded_interval64_covers_object_q word5 object5`
  >> qexists_tac
       `bounded_object_q_delta_hessian_six_cv
          object0 object1 object2 object3 object4 object5`
  >> simp [bounded_object_q_delta_hessian_cv_def]
  >> metis_tac
       [compute_boundedAnalyticObjectDeltaHessianRefinementTheory.bounded_delta64_hessian_six_covers_object_q]
QED

Theorem bounded_nth_list_rel:
  !relation word_values object_values index word_value.
    LIST_REL relation word_values object_values /\
    bounded_interval64_nth word_values index = SOME word_value ==>
    ?object_value.
      bounded_object_q_nth object_values index = SOME object_value /\
      relation word_value object_value
Proof
  Induct_on `word_values`
  >> Cases_on `object_values`
  >> Cases_on `index`
  >> rw [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def,
         compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_nth_def]
  >> gvs [LIST_REL_def]
  >> metis_tac []
QED

Definition bounded_object_q_taylor_complete_cv_def:
  bounded_object_q_taylor_complete_cv radii weights result_domain
      center_value center_gradient hessian =
    BoundedObjectQTaylor result_domain center_value center_gradient
      (bounded_object_q_taylor_value_complete_cv center_value
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian))
      (bounded_object_q_taylor_gradient_complete_cv
        radii center_gradient hessian)
      hessian
End

Theorem bounded_taylor64_complete_refines_object_q_taylor:
  bounded_interval64_covers_object_q word_center object_center /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_gradient object_center_gradient /\
  LIST_REL bounded_interval64_covers_object_q
    word_hessian object_hessian /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_complete radii result_domain word_center
    word_center_gradient word_hessian = SOME word_result ==>
  bounded_taylor64_covers_object_q word_result
    (bounded_object_q_taylor_complete_cv radii weights result_domain
      object_center object_center_gradient object_hessian)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectTaylorRefinementTheory.bounded_taylor64_complete_covers_object_q_state
  >> gvs [bounded_object_q_taylor_complete_cv_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
QED

val _ = export_theory ();
