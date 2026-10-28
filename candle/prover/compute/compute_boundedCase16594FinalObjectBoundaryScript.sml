(*****************************************************************************
 * Exact final-object boundary for the genuine case-16594 analytic plan.
 *****************************************************************************)
Theory compute_boundedCase16594FinalObjectBoundary
Ancestors
  compute_boundedAnalyticObjectFinalAddRefinement
  compute_boundedCase16594PreparedPlan
Libs
  bossLib preamble

Definition bounded_case16594_source_prefix_def:
  bounded_case16594_source_prefix = FRONT bounded_case16594_program
End

Definition bounded_case16594_prepared_prefix_def:
  bounded_case16594_prepared_prefix =
    FRONT bounded_case16594_prepared_program
End

Theorem bounded_case16594_final_add_boundary:
  bounded_case16594_program =
    bounded_case16594_source_prefix ++ [BoundedAnalyticAdd] /\
  bounded_case16594_prepared_program =
    bounded_case16594_prepared_prefix ++ [BoundedAnalytic64Add] /\
  LENGTH bounded_case16594_source_prefix =
    LENGTH bounded_case16594_prepared_prefix
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_object_run_value_complete:
  bounded_object_q_analytic_run radii weights object_center_environment
    object_box_environment bounded_case16594_program
    bounded_case16594_prepared_program object_start
    ([BoundedObjectQTaylor object_domain object_center
        object_center_gradient object_value_bound object_gradient_bounds
        object_hessian],[]) ==>
  object_value_bound =
    bounded_object_q_taylor_value_complete_cv object_center
      (bounded_object_q_taylor_error_cv radii object_center_gradient weights
        object_hessian)
Proof
  metis_tac
    [bounded_case16594_final_add_boundary,
     compute_boundedAnalyticObjectFinalAddRefinementTheory.bounded_object_q_analytic_run_final_add_complete]
QED

val _ = export_theory ();
