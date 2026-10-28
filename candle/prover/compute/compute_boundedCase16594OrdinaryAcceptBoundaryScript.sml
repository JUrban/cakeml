(*****************************************************************************
 * Genuine case-16594 packed acceptance reaches the ordinary Candle exact-q
 * six-dimensional acceptance contract.
 *****************************************************************************)
Theory compute_boundedCase16594OrdinaryAcceptBoundary
Ancestors
  compute_boundedPackedObjectAcceptRefinement
  compute_boundedCase16594AcceptedObjectBoundary
Libs
  bossLib preamble

Theorem bounded_case16594_packed_cell_ordinary_accept6:
  bounded_packed_analytic_object_cell bounded_case16594_program
      bounded_case16594_prepared_program
      ((box_environment,center_environment,radii),certificates) ==>
  ?weights word_result object_domain object_center_value object_center_gradient
   object_gradient_bounds object_hessian.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_analytic64_program_eval radii center_environment box_environment
      bounded_case16594_prepared_program certificates = SOME word_result /\
    bounded_taylor64_covers_object_q word_result
      (BoundedObjectQTaylor object_domain object_center_value
        object_center_gradient
        (bounded_object_q_taylor_value_complete_cv object_center_value
          (bounded_object_q_taylor_error_cv radii object_center_gradient
            weights object_hessian))
        object_gradient_bounds object_hessian) /\
    bounded_object_q_ordinary_accept6 object_domain radii
      object_center_value object_center_gradient weights object_hessian
Proof
  strip_tac
  >> drule
       compute_boundedCase16594AcceptedObjectBoundaryTheory.bounded_case16594_packed_cell_completed_negative
  >> strip_tac
  >> `bounded_taylor64_well_formed word_result` by
       metis_tac
         [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some]
  >> `bounded_object_q_ordinary_accept6 object_domain radii
        object_center_value object_center_gradient weights object_hessian` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_packed_object_completed_negative_refines_ordinary_accept6]
  >> metis_tac []
QED

val _ = export_theory ();
