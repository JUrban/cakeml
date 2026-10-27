(*****************************************************************************
 * Object-q refinement for the generic scale-2^40 unary Taylor chain rule.
 *
 * The proof-only witnesses below mirror list scaling and the compact
 * symmetric self-outer product without adding executable runtime code.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectUnaryRefinement
Ancestors
  compute_boundedAnalyticObjectTaylorRefinement
Libs
  bossLib preamble

Definition bounded_object_q_interval_list_scale_cv_def:
  bounded_object_q_interval_list_scale_cv scalar values =
    MAP (bounded_object_q_interval_mul_cv scalar) values
End

Theorem bounded_interval64_list_scale_covers_object_q:
  !values object_values result.
    bounded_interval64_covers_object_q scalar object_scalar /\
    LIST_REL bounded_interval64_covers_object_q values object_values /\
    bounded_interval64_list_scale scalar values = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_list_scale_cv object_scalar object_values)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedIntervalListTheory.bounded_interval64_list_scale_def,
         bounded_object_q_interval_list_scale_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q
  >> res_tac
  >> fs [bounded_object_q_interval_list_scale_cv_def]
QED

Definition bounded_object_q_interval_self_outer_cv_def:
  bounded_object_q_interval_self_outer_cv [] = [] /\
  bounded_object_q_interval_self_outer_cv (entry::rest) =
    bounded_object_q_interval_list_scale_cv entry (entry::rest) ++
    bounded_object_q_interval_self_outer_cv rest
End

Theorem bounded_interval64_self_outer_covers_object_q:
  !values object_values result.
    LIST_REL bounded_interval64_covers_object_q values object_values /\
    bounded_interval64_self_outer values = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_self_outer_cv object_values)
Proof
  Induct
  >> Cases_on `object_values`
  >> rw [compute_boundedTaylorUnaryTheory.bounded_interval64_self_outer_def,
         bounded_object_q_interval_self_outer_cv_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac bounded_interval64_list_scale_covers_object_q
  >> res_tac
  >> irule listTheory.LIST_REL_APPEND_suff
  >> simp []
QED

Theorem bounded_taylor64_unary_complete_trace:
  bounded_taylor64_unary_complete radii result_domain center_result
      center_derivative box_derivative box_second source = SOME result ==>
  ?source_domain source_center source_center_gradient source_value
      source_gradient_bounds source_hessian center_gradient gradient_outer
      outer_hessian source_hessian_scaled hessian.
    source =
      BoundedTaylor64 source_domain source_center source_center_gradient
        source_value source_gradient_bounds source_hessian /\
    bounded_interval64_list_scale center_derivative
      source_center_gradient = SOME center_gradient /\
    bounded_interval64_self_outer source_gradient_bounds =
      SOME gradient_outer /\
    bounded_interval64_list_scale box_second gradient_outer =
      SOME outer_hessian /\
    bounded_interval64_list_scale box_derivative source_hessian =
      SOME source_hessian_scaled /\
    bounded_interval64_list_add outer_hessian source_hessian_scaled =
      SOME hessian /\
    bounded_taylor64_complete radii
      (source_domain /\ result_domain) center_result center_gradient
      hessian = SOME result
Proof
  Cases_on `source`
  >> rw [compute_boundedTaylorUnaryTheory.bounded_taylor64_unary_complete_def]
  >> every_case_tac
  >> gvs []
  >> rpt (first_assum (irule_at Any))
QED

Definition bounded_object_q_taylor_unary_hessian_cv_def:
  bounded_object_q_taylor_unary_hessian_cv box_derivative box_second
      source_gradient_bounds source_hessian =
    MAP2 bounded_object_q_interval_add_cv
      (bounded_object_q_interval_list_scale_cv box_second
        (bounded_object_q_interval_self_outer_cv source_gradient_bounds))
      (bounded_object_q_interval_list_scale_cv box_derivative source_hessian)
End

Theorem bounded_taylor64_unary_reaches_object_q_complete_inputs:
  bounded_taylor64_covers_object_q_state source object_source_domain
      object_source_center object_source_center_gradient object_source_value
      object_source_gradient_bounds object_source_hessian /\
  result_domain = object_result_domain /\
  bounded_interval64_covers_object_q center_result object_center_result /\
  bounded_interval64_covers_object_q
      center_derivative object_center_derivative /\
  bounded_interval64_covers_object_q box_derivative object_box_derivative /\
  bounded_interval64_covers_object_q box_second object_box_second /\
  bounded_taylor64_unary_complete radii result_domain center_result
      center_derivative box_derivative box_second source = SOME result ==>
  ?center_gradient hessian.
    bounded_taylor64_complete radii
      (object_source_domain /\ object_result_domain)
      center_result center_gradient hessian = SOME result /\
    bounded_taylor64_complete_inputs_cover_object_q
      (object_source_domain /\ object_result_domain)
      center_result center_gradient hessian
      (object_source_domain /\ object_result_domain)
      object_center_result
      (bounded_object_q_interval_list_scale_cv object_center_derivative
        object_source_center_gradient)
      (bounded_object_q_taylor_unary_hessian_cv object_box_derivative
        object_box_second object_source_gradient_bounds
        object_source_hessian)
Proof
  strip_tac
  >> drule bounded_taylor64_unary_complete_trace
  >> strip_tac
  >> gvs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> `LIST_REL bounded_interval64_covers_object_q center_gradient
        (bounded_object_q_interval_list_scale_cv object_center_derivative
          object_source_center_gradient)` by
       (match_mp_tac
          (Q.INST
            [`scalar` |-> `center_derivative`,
             `object_scalar` |-> `object_center_derivative`]
            (Q.SPECL
              [`source_center_gradient`, `object_source_center_gradient`,
               `center_gradient`]
              bounded_interval64_list_scale_covers_object_q))
        >> simp [])
  >> `LIST_REL bounded_interval64_covers_object_q gradient_outer
        (bounded_object_q_interval_self_outer_cv
          object_source_gradient_bounds)` by
       (match_mp_tac
          (Q.SPECL
            [`source_gradient_bounds`, `object_source_gradient_bounds`,
             `gradient_outer`]
            bounded_interval64_self_outer_covers_object_q)
        >> simp [])
  >> `LIST_REL bounded_interval64_covers_object_q outer_hessian
        (bounded_object_q_interval_list_scale_cv object_box_second
          (bounded_object_q_interval_self_outer_cv
            object_source_gradient_bounds))` by
       (match_mp_tac
          (Q.INST
            [`scalar` |-> `box_second`,
             `object_scalar` |-> `object_box_second`]
            (Q.SPECL
              [`gradient_outer`,
               `bounded_object_q_interval_self_outer_cv
                  object_source_gradient_bounds`, `outer_hessian`]
              bounded_interval64_list_scale_covers_object_q))
        >> simp [])
  >> `LIST_REL bounded_interval64_covers_object_q source_hessian_scaled
        (bounded_object_q_interval_list_scale_cv object_box_derivative
          object_source_hessian)` by
       (match_mp_tac
          (Q.INST
            [`scalar` |-> `box_derivative`,
             `object_scalar` |-> `object_box_derivative`]
            (Q.SPECL
              [`source_hessian`, `object_source_hessian`,
               `source_hessian_scaled`]
              bounded_interval64_list_scale_covers_object_q))
        >> simp [])
  >> `LIST_REL bounded_interval64_covers_object_q hessian
        (MAP2 bounded_object_q_interval_add_cv
          (bounded_object_q_interval_list_scale_cv object_box_second
            (bounded_object_q_interval_self_outer_cv
              object_source_gradient_bounds))
          (bounded_object_q_interval_list_scale_cv object_box_derivative
            object_source_hessian))` by
       (match_mp_tac
          (Q.SPECL
            [`outer_hessian`, `source_hessian_scaled`,
             `bounded_object_q_interval_list_scale_cv object_box_second
                (bounded_object_q_interval_self_outer_cv
                  object_source_gradient_bounds)`,
             `bounded_object_q_interval_list_scale_cv object_box_derivative
                object_source_hessian`, `hessian`]
            compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_list_add_covers_object_q)
        >> simp [])
  >> qexists_tac `center_gradient`
  >> qexists_tac `hessian`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_taylor64_complete_inputs_cover_object_q_def,
        bounded_object_q_taylor_unary_hessian_cv_def]
QED

Theorem bounded_taylor64_unary_covers_object_q_state:
  bounded_taylor64_covers_object_q_state source object_source_domain
      object_source_center object_source_center_gradient object_source_value
      object_source_gradient_bounds object_source_hessian /\
  result_domain = object_result_domain /\
  bounded_interval64_covers_object_q center_result object_center_result /\
  bounded_interval64_covers_object_q
      center_derivative object_center_derivative /\
  bounded_interval64_covers_object_q box_derivative object_box_derivative /\
  bounded_interval64_covers_object_q box_second object_box_second /\
  bounded_taylor64_unary_complete radii result_domain center_result
      center_derivative box_derivative box_second source = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result
      (object_source_domain /\ object_result_domain)
      object_center_result
      (bounded_object_q_interval_list_scale_cv object_center_derivative
        object_source_center_gradient)
      (bounded_object_q_taylor_value_complete_cv object_center_result
        (bounded_object_q_taylor_error_cv radii
          (bounded_object_q_interval_list_scale_cv object_center_derivative
            object_source_center_gradient)
          weights
          (bounded_object_q_taylor_unary_hessian_cv object_box_derivative
            object_box_second object_source_gradient_bounds
            object_source_hessian)))
      (bounded_object_q_taylor_gradient_complete_cv radii
        (bounded_object_q_interval_list_scale_cv object_center_derivative
          object_source_center_gradient)
        (bounded_object_q_taylor_unary_hessian_cv object_box_derivative
          object_box_second object_source_gradient_bounds
          object_source_hessian))
      (bounded_object_q_taylor_unary_hessian_cv object_box_derivative
        object_box_second object_source_gradient_bounds
        object_source_hessian)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`source` |-> `source`, `object_source_domain` |-> `object_source_domain`,
          `object_source_center` |-> `object_source_center`,
          `object_source_center_gradient` |-> `object_source_center_gradient`,
          `object_source_value` |-> `object_source_value`,
          `object_source_gradient_bounds` |-> `object_source_gradient_bounds`,
          `object_source_hessian` |-> `object_source_hessian`,
          `result_domain` |-> `result_domain`,
          `object_result_domain` |-> `object_result_domain`,
          `center_result` |-> `center_result`,
          `object_center_result` |-> `object_center_result`,
          `center_derivative` |-> `center_derivative`,
          `object_center_derivative` |-> `object_center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `object_box_derivative` |-> `object_box_derivative`,
          `box_second` |-> `box_second`,
          `object_box_second` |-> `object_box_second`,
          `radii` |-> `radii`, `result` |-> `result`]
         bounded_taylor64_unary_reaches_object_q_complete_inputs)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `center_gradient`
         (qx_choose_then `hessian` strip_assume_tac))
  >> fs
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_taylor64_complete_inputs_cover_object_q_def]
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`,
          `result_domain` |->
            `object_source_domain /\ object_result_domain`,
          `center_value` |-> `center_result`,
          `object_center_value` |-> `object_center_result`,
          `center_gradient` |-> `center_gradient`,
          `object_center_gradient` |->
            `bounded_object_q_interval_list_scale_cv
              object_center_derivative object_source_center_gradient`,
          `hessian` |-> `hessian`,
          `object_hessian` |->
            `bounded_object_q_taylor_unary_hessian_cv
              object_box_derivative object_box_second
              object_source_gradient_bounds object_source_hessian`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectTaylorRefinementTheory.bounded_taylor64_complete_covers_object_q_state)
  >> simp []
QED

val _ = export_theory ();
