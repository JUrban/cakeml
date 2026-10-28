(*****************************************************************************
 * Exact completed-bound sign for one accepted genuine case-16594 cell.
 *****************************************************************************)
Theory compute_boundedCase16594AcceptedObjectBoundary
Ancestors
  compute_boundedPackedAnalyticNegativeBoundary
  compute_boundedCase16594FinalObjectBoundary
Libs
  bossLib preamble

Theorem bounded_case16594_packed_cell_completed_negative:
  bounded_packed_analytic_object_cell bounded_case16594_program
      bounded_case16594_prepared_program
      ((box_environment,center_environment,radii),certificates) ==>
  ?weights word_result object_domain object_center_value object_center_gradient
   object_gradient_bounds object_hessian.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_analytic64_program_eval radii center_environment box_environment
      bounded_case16594_prepared_program certificates = SOME word_result /\
    bounded_packed_analytic_result_accepts word_result /\
    bounded_object_q_analytic_run radii weights
      (MAP bounded_interval64_object_q_cv center_environment)
      (MAP bounded_interval64_object_q_cv box_environment)
      bounded_case16594_program bounded_case16594_prepared_program
      ([],certificates)
      ([BoundedObjectQTaylor object_domain object_center_value
          object_center_gradient
          (bounded_object_q_taylor_value_complete_cv object_center_value
            (bounded_object_q_taylor_error_cv radii object_center_gradient
              weights object_hessian))
          object_gradient_bounds object_hessian],[]) /\
    bounded_taylor64_covers_object_q word_result
      (BoundedObjectQTaylor object_domain object_center_value
        object_center_gradient
        (bounded_object_q_taylor_value_complete_cv object_center_value
          (bounded_object_q_taylor_error_cv radii object_center_gradient
            weights object_hessian))
        object_gradient_bounds object_hessian) /\
    object_domain /\
    bounded_object_q_interval_upper_strict_negative
      (bounded_object_q_taylor_value_complete_cv object_center_value
        (bounded_object_q_taylor_error_cv radii object_center_gradient
          weights object_hessian))
Proof
  metis_tac
    [compute_boundedPackedAnalyticNegativeBoundaryTheory.bounded_packed_analytic_object_cell_negative,
     compute_boundedCase16594FinalObjectBoundaryTheory.bounded_case16594_object_run_value_complete]
QED

val _ = export_theory ();
