(*****************************************************************************
 * Independent fixed-word witness soundness for genuine case-16594 cell 0.
 *
 * The 31 fixed-word certificates are untrusted witnesses checked by the
 * 167-instruction evaluator.  They need not equal the legacy exact-rational
 * certificate payload.  This theory connects the successful word evaluation
 * to the authenticated source program and authenticated object-q input box by
 * the generic program-refinement theorem.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedWordObjectBridge
Ancestors
  compute_boundedCase16594Cell0RuntimePayloadIdentity
  compute_boundedCase16594DispatchPlanIdentity
  compute_boundedAnalyticObjectProgramRunRefinement
  compute_boundedPackedAnalyticNegativeBoundary
  compute_boundedCase16594FinalObjectBoundary
  compute_boundedPackedObjectAcceptRefinement
  compute_boundedPackedObjectSourceContractRefinement
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_cell0_authenticated_word_weights_def:
  bounded_case16594_cell0_authenticated_word_weights =
    THE
      (bounded_taylor_radius_pairs
        bounded_case16594_cell0_source_word_radii)
End

Theorem bounded_case16594_cell0_authenticated_word_radius_pairs:
  bounded_taylor_radius_pairs bounded_case16594_cell0_source_word_radii =
    SOME bounded_case16594_cell0_authenticated_word_weights
Proof
  simp
    [bounded_case16594_cell0_authenticated_word_weights_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_radii_def,
     compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def]
QED

Theorem bounded_case16594_cell0_authenticated_word_object_run:
  ?object_result.
    bounded_object_q_analytic_run
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_program bounded_case16594_prepared_program
      ([],bounded_case16594_cell0_source_word_certificates)
      ([object_result],[]) /\
    bounded_taylor64_covers_object_q
      bounded_case16594_cell0_authenticated_word_result object_result
Proof
  irule
    compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_analytic64_program_eval_refines_object_q
  >> simp
    [compute_boundedCase16594DispatchPlanIdentityTheory.bounded_case16594_dispatch_plan_refines,
     bounded_case16594_cell0_authenticated_word_radius_pairs]
  >> qexists_tac `bounded_case16594_cell0_authenticated_word_box_environment`
  >> qexists_tac `bounded_case16594_cell0_source_word_center_environment`
  >> simp
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_covers_authenticated,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_covers_authenticated,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_program_eval]
QED

Theorem bounded_case16594_cell0_authenticated_word_result_accepts:
  bounded_packed_analytic_result_accepts
    bounded_case16594_cell0_authenticated_word_result
Proof
  rw
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_result_def,
     compute_boundedPackedAnalyticCheckTheory.bounded_packed_analytic_result_accepts_def,
     compute_boundedIntervalTheory.bounded_interval64_upper_def,
     compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
     compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def]
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_cell0_authenticated_word_completed_negative:
  ?object_domain object_center_value object_center_gradient
   object_gradient_bounds object_hessian.
    bounded_object_q_analytic_run
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_program bounded_case16594_prepared_program
      ([],bounded_case16594_cell0_source_word_certificates)
      ([BoundedObjectQTaylor object_domain object_center_value
          object_center_gradient
          (bounded_object_q_taylor_value_complete_cv object_center_value
            (bounded_object_q_taylor_error_cv
              bounded_case16594_cell0_source_word_radii
              object_center_gradient
              bounded_case16594_cell0_authenticated_word_weights
              object_hessian))
          object_gradient_bounds object_hessian],[]) /\
    bounded_taylor64_covers_object_q
      bounded_case16594_cell0_authenticated_word_result
      (BoundedObjectQTaylor object_domain object_center_value
        object_center_gradient
        (bounded_object_q_taylor_value_complete_cv object_center_value
          (bounded_object_q_taylor_error_cv
            bounded_case16594_cell0_source_word_radii
            object_center_gradient
            bounded_case16594_cell0_authenticated_word_weights
            object_hessian))
        object_gradient_bounds object_hessian) /\
    object_domain /\
    bounded_object_q_interval_upper_strict_negative
      (bounded_object_q_taylor_value_complete_cv object_center_value
        (bounded_object_q_taylor_error_cv
          bounded_case16594_cell0_source_word_radii object_center_gradient
          bounded_case16594_cell0_authenticated_word_weights object_hessian))
Proof
  mp_tac bounded_case16594_cell0_authenticated_word_object_run
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> Cases_on `object_result`
  >> metis_tac
    [bounded_case16594_cell0_authenticated_word_result_accepts,
     compute_boundedPackedAnalyticNegativeBoundaryTheory.bounded_packed_analytic_result_accepts_object_q_negative,
     compute_boundedCase16594FinalObjectBoundaryTheory.bounded_case16594_object_run_value_complete]
QED

Theorem bounded_case16594_cell0_authenticated_word_ordinary_accept6:
  ?object_domain object_center_value object_center_gradient
   object_gradient_bounds object_hessian.
    bounded_object_q_analytic_run
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_program bounded_case16594_prepared_program
      ([],bounded_case16594_cell0_source_word_certificates)
      ([BoundedObjectQTaylor object_domain object_center_value
          object_center_gradient
          (bounded_object_q_taylor_value_complete_cv object_center_value
            (bounded_object_q_taylor_error_cv
              bounded_case16594_cell0_source_word_radii
              object_center_gradient
              bounded_case16594_cell0_authenticated_word_weights
              object_hessian))
          object_gradient_bounds object_hessian],[]) /\
    bounded_taylor64_covers_object_q
      bounded_case16594_cell0_authenticated_word_result
      (BoundedObjectQTaylor object_domain object_center_value
        object_center_gradient
        (bounded_object_q_taylor_value_complete_cv object_center_value
          (bounded_object_q_taylor_error_cv
            bounded_case16594_cell0_source_word_radii
            object_center_gradient
            bounded_case16594_cell0_authenticated_word_weights
            object_hessian))
        object_gradient_bounds object_hessian) /\
    bounded_object_q_ordinary_accept6 object_domain
      bounded_case16594_cell0_source_word_radii object_center_value
      object_center_gradient
      bounded_case16594_cell0_authenticated_word_weights object_hessian
Proof
  mp_tac bounded_case16594_cell0_authenticated_word_completed_negative
  >> strip_tac
  >> `bounded_taylor64_well_formed
        bounded_case16594_cell0_authenticated_word_result` by
       metis_tac
         [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some,
          compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_program_eval]
  >> rpt (first_assum $ irule_at Any)
  >> metis_tac
    [bounded_case16594_cell0_authenticated_word_radius_pairs,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_packed_object_completed_negative_refines_ordinary_accept6]
QED

Theorem bounded_case16594_cell0_authenticated_word_source_accept6:
  ?object_domain object_center_value object_center_gradient
   object_gradient_bounds object_hessian.
    bounded_object_q_analytic_run
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_program bounded_case16594_prepared_program
      ([],bounded_case16594_cell0_source_word_certificates)
      ([BoundedObjectQTaylor object_domain object_center_value
          object_center_gradient
          (bounded_object_q_taylor_value_complete_cv object_center_value
            (bounded_object_q_taylor_error_cv
              bounded_case16594_cell0_source_word_radii
              object_center_gradient
              bounded_case16594_cell0_authenticated_word_weights
              object_hessian))
          object_gradient_bounds object_hessian],[]) /\
    bounded_taylor64_covers_object_q
      bounded_case16594_cell0_authenticated_word_result
      (BoundedObjectQTaylor object_domain object_center_value
        object_center_gradient
        (bounded_object_q_taylor_value_complete_cv object_center_value
          (bounded_object_q_taylor_error_cv
            bounded_case16594_cell0_source_word_radii
            object_center_gradient
            bounded_case16594_cell0_authenticated_word_weights
            object_hessian))
        object_gradient_bounds object_hessian) /\
    bounded_packed_object_source_accept6
      (MAP bounded_word64_object_q_cv
        bounded_case16594_cell0_source_word_radii)
      object_center_value object_center_gradient object_hessian
Proof
  mp_tac bounded_case16594_cell0_authenticated_word_ordinary_accept6
  >> strip_tac
  >> rpt (first_assum $ irule_at Any)
  >> metis_tac
    [bounded_case16594_cell0_authenticated_word_radius_pairs,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_object_ordinary_accept_refines_source]
QED

val _ = export_theory ();
