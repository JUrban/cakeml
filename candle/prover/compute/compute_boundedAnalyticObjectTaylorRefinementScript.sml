(*****************************************************************************
 * Object-q refinement for the complete scale-2^40 Taylor constructor.
 *
 * The value and gradient completion refinements are proved independently.
 * This proof-only composition packages them as the state invariant consumed
 * by the generic source-program induction.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectTaylorRefinement
Ancestors
  compute_boundedAnalyticObjectGradientRefinement
Libs
  bossLib preamble

Theorem bounded_taylor64_complete_covers_object_q_state:
  bounded_interval64_covers_object_q center_value object_center_value /\
  LIST_REL bounded_interval64_covers_object_q
      center_gradient object_center_gradient /\
  LIST_REL bounded_interval64_covers_object_q hessian object_hessian /\
  bounded_taylor64_complete radii result_domain center_value center_gradient
      hessian = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result result_domain
      object_center_value object_center_gradient
      (bounded_object_q_taylor_value_complete_cv object_center_value
        (bounded_object_q_taylor_error_cv
          radii object_center_gradient weights object_hessian))
      (bounded_object_q_taylor_gradient_complete_cv
        radii object_center_gradient object_hessian)
      object_hessian
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_taylor64_complete_def]
  >> every_case_tac
  >> gvs [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
          compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> metis_tac
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_taylor_value_complete_covers_object_q,
        bounded_taylor_gradient_complete_covers_object_q]
QED

val _ = export_theory ();
