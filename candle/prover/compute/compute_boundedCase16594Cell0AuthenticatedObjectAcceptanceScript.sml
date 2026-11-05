(*****************************************************************************
 * Acceptance boundary for the complete genuine-cell fast object trace.
 *
 * This connects the 167 checked actions to the production runtime state and
 * transports the final source-level acceptance contract across normalized
 * rational representations.  It deliberately uses the authenticated fast
 * certificate stream, not the distinct legacy entry payload.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectAcceptance
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectCompleteTrace
  compute_boundedCase16594ObjectRuntimeAcceptTransfer
Libs
  bossLib preamble wordsLib

Theorem bounded_case16594_cell0_authenticated_object_semantic_accept:
  ?runtime_stack object_center object_center_gradient object_value_bound
      object_gradient_bounds object_hessian.
    bounded_case16594_object_dispatch_semantic_trace 524405
      bounded_case16594_runtime_cell0_center_boxes_cv
      bounded_case16594_runtime_cell0_outer_boxes_cv
      bounded_case16594_runtime_cell0_radii_cv
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_authenticated_word_weights
      bounded_case16594_cell0_authenticated_object_center_environment
      bounded_case16594_cell0_authenticated_object_box_environment
      bounded_case16594_program bounded_case16594_prepared_program
      bounded_case16594_runtime_cell0_codes_cv
      bounded_case16594_runtime_cell0_sources_cv
      bounded_case16594_cell0_fast_object_certificates_cv []
      ([],bounded_case16594_cell0_source_word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list runtime_stack) (Num 0)))
      ([BoundedObjectQTaylor T object_center object_center_gradient
          object_value_bound object_gradient_bounds object_hessian],[]) /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack
      [BoundedObjectQTaylor T object_center object_center_gradient
        object_value_bound object_gradient_bounds object_hessian] /\
    bounded_packed_object_source_accept6
      (MAP bounded_word64_object_q_cv
        bounded_case16594_cell0_source_word_radii)
      object_center object_center_gradient object_hessian
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectCompleteTraceTheory.bounded_case16594_cell0_authenticated_object_complete_trace
  >> disch_then
       (qx_choose_then `semantic_after`
         (qx_choose_then `runtime_stack` strip_assume_tac))
  >> `bounded_object_q_analytic_run
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_program bounded_case16594_prepared_program
        ([],bounded_case16594_cell0_source_word_certificates)
        semantic_after` by
       metis_tac
         [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_projects_run]
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack
        (FST semantic_after)` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectFirstSpecializedPairTraceTheory.bounded_case16594_named_semantic_trace_final_stack]
  >> PairCases_on `semantic_after`
  >> Cases_on `semantic_after0`
  >- gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        LIST_REL_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_final_state_shape]
  >> Cases_on `t`
  >> gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        LIST_REL_def,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_final_state_shape]
  >> Cases_on `h`
  >> rename1
       `bounded_taylor64_covers_object_q
          bounded_case16594_cell0_authenticated_word_result
          (BoundedObjectQTaylor object_domain object_center
            object_center_gradient object_value_bound object_gradient_bounds
            object_hessian)`
  >> `object_value_bound =
        bounded_object_q_taylor_value_complete_cv object_center
          (bounded_object_q_taylor_error_cv
            bounded_case16594_cell0_source_word_radii object_center_gradient
            bounded_case16594_cell0_authenticated_word_weights
            object_hessian)` by
       metis_tac
         [compute_boundedCase16594FinalObjectBoundaryTheory.bounded_case16594_object_run_value_complete]
  >> `object_domain /\
        bounded_object_q_interval_upper_strict_negative object_value_bound` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_result_accepts,
          compute_boundedPackedAnalyticNegativeBoundaryTheory.bounded_packed_analytic_result_accepts_object_q_negative]
  >> `bounded_taylor64_well_formed
        bounded_case16594_cell0_authenticated_word_result` by
       metis_tac
         [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some,
          compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_program_eval]
  >> `bounded_object_q_ordinary_accept6 object_domain
        bounded_case16594_cell0_source_word_radii object_center
        object_center_gradient
        bounded_case16594_cell0_authenticated_word_weights object_hessian` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_packed_object_completed_negative_refines_ordinary_accept6]
  >> `bounded_packed_object_source_accept6
        (MAP bounded_word64_object_q_cv
          bounded_case16594_cell0_source_word_radii)
        object_center object_center_gradient object_hessian` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs,
          compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_object_ordinary_accept_refines_source]
  >> qexists_tac `runtime_stack`
  >> qexists_tac `object_center`
  >> qexists_tac `object_center_gradient`
  >> qexists_tac `object_value_bound`
  >> qexists_tac `object_gradient_bounds`
  >> qexists_tac `object_hessian`
  >> gvs []
QED

Theorem bounded_object_q_taylor_stack_runtime_refines_singleton:
  bounded_object_q_taylor_stack_runtime_refines runtime_stack [semantic] ==>
  ?runtime_state.
    runtime_stack = [runtime_state] /\
    bounded_object_q_taylor_runtime_refines runtime_state semantic
Proof
  Cases_on `runtime_stack`
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
  >> Cases_on `t`
  >> fs [LIST_REL_def]
QED

Theorem bounded_case16594_cell0_authenticated_object_accepted_program_eval:
  ?runtime_state runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    compute_eval compute_default_clock
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_program»
        [from_cv bounded_case16594_runtime_cell0_center_boxes_cv;
         from_cv bounded_case16594_runtime_cell0_outer_boxes_cv;
         from_cv bounded_case16594_runtime_cell0_radii_cv;
         from_cv bounded_case16594_runtime_cell0_codes_cv;
         from_cv bounded_case16594_runtime_cell0_sources_cv;
         from_cv bounded_case16594_cell0_fast_object_certificates_cv;
         from_cv (Num 0)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (Pair (bounded_object_q_cv_list [runtime_state]) (Num 0)))),
       refs) /\
    runtime_state =
      bounded_case16594_object_state_cv (Num 1) runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    bounded_packed_object_source_accept6
      bounded_case16594_cell0_authenticated_object_radii
      runtime_center runtime_center_gradient runtime_hessian
Proof
  mp_tac bounded_case16594_cell0_authenticated_object_semantic_accept
  >> disch_then
       (qx_choose_then `runtime_stack`
         (qx_choose_then `object_center`
           (qx_choose_then `object_center_gradient`
             (qx_choose_then `object_value_bound`
               (qx_choose_then `object_gradient_bounds`
                 (qx_choose_then `object_hessian` strip_assume_tac))))))
  >> `?runtime_state.
        runtime_stack = [runtime_state] /\
        bounded_object_q_taylor_runtime_refines runtime_state
          (BoundedObjectQTaylor T object_center object_center_gradient
            object_value_bound object_gradient_bounds object_hessian)` by
       metis_tac [bounded_object_q_taylor_stack_runtime_refines_singleton]
  >> `bounded_case16594_object_dispatch_semantic_trace 524405
        bounded_case16594_runtime_cell0_center_boxes_cv
        bounded_case16594_runtime_cell0_outer_boxes_cv
        bounded_case16594_runtime_cell0_radii_cv
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_authenticated_word_weights
        bounded_case16594_cell0_authenticated_object_center_environment
        bounded_case16594_cell0_authenticated_object_box_environment
        bounded_case16594_program bounded_case16594_prepared_program
        bounded_case16594_runtime_cell0_codes_cv
        bounded_case16594_runtime_cell0_sources_cv
        bounded_case16594_cell0_fast_object_certificates_cv []
        ([],bounded_case16594_cell0_source_word_certificates)
        (Pair (Num 1)
          (Pair (bounded_object_q_cv_list [runtime_state]) (Num 0)))
        ([BoundedObjectQTaylor T object_center object_center_gradient
            object_value_bound object_gradient_bounds object_hessian],[])` by
       metis_tac []
  >> mp_tac
       (Q.INST
         [`semantic_radii` |->
            `MAP bounded_word64_object_q_cv
              bounded_case16594_cell0_source_word_radii`,
          `runtime_radii` |->
            `bounded_case16594_cell0_authenticated_object_radii`,
          `semantic_center` |-> `object_center`,
          `semantic_center_gradient` |-> `object_center_gradient`,
          `semantic_value_bound` |-> `object_value_bound`,
          `semantic_gradient_bounds` |-> `object_gradient_bounds`,
          `semantic_hessian` |-> `object_hessian`,
          `runtime_state` |-> `runtime_state`]
         compute_boundedCase16594ObjectRuntimeAcceptTransferTheory.bounded_object_q_taylor_runtime_refines_source_accept6)
  >> impl_tac
  >- metis_tac
       [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_equivalent]
  >> disch_then
       (qx_choose_then `runtime_center`
         (qx_choose_then `runtime_center_gradient`
           (qx_choose_then `runtime_value_bound`
             (qx_choose_then `runtime_gradient_bounds`
               (qx_choose_then `runtime_hessian` strip_assume_tac)))))
  >> `compute_eval compute_default_clock
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_dispatch_program»
          [from_cv bounded_case16594_runtime_cell0_center_boxes_cv;
           from_cv bounded_case16594_runtime_cell0_outer_boxes_cv;
           from_cv bounded_case16594_runtime_cell0_radii_cv;
           from_cv bounded_case16594_runtime_cell0_codes_cv;
           from_cv bounded_case16594_runtime_cell0_sources_cv;
           from_cv bounded_case16594_cell0_fast_object_certificates_cv;
           from_cv (bounded_object_q_cv_list [])]) refs =
        (M_success
          (from_cv
            (Pair (Num 1)
              (Pair (bounded_object_q_cv_list [runtime_state]) (Num 0)))),
         refs)` by
       (irule
          compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_eval
        >> metis_tac
             [compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_object_dispatch_cell0_default_clock_capacity])
  >> `(Num 0:cv) = bounded_object_q_cv_list []` by
       simp
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> qexists_tac `runtime_state`
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> metis_tac []
QED

val _ = export_theory ();
