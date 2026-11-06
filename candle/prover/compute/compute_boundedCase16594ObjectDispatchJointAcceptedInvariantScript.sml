(*****************************************************************************
 * Accepted arbitrary-cell endpoint for the complete joint case-16594 trace.
 *
 * A successful fixed-word trace whose singleton result passes the exact
 * packed acceptance test yields a singleton production runtime state and the
 * representation-independent six-dimensional source-acceptance predicate.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointAcceptedInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchJointCompleteInvariant
  compute_boundedCase16594ObjectRuntimeAcceptTransfer
  compute_boundedCase16594FinalObjectBoundary
  compute_boundedPackedAnalyticNegativeBoundary
Libs
  bossLib preamble intLib

Theorem bounded_object_q_taylor_stack_runtime_refines_singleton_general:
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

Theorem bounded_case16594_object_joint_complete_accepted_runtime_state:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LENGTH semantic_center_boxes = 6 /\
  LENGTH semantic_outer_boxes = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    semantic_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    semantic_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_runtime_certificate_trace semantic_radii
    word_center_boxes word_outer_boxes bounded_case16594_prepared_program
    ([],word_certificates) = SOME (([word_result],[]),packets) /\
  bounded_case16594_word_dispatch_packet_contracts
    word_certificates packets /\
  bounded_packed_analytic_result_accepts word_result
  ==>
  ?runtime_state runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian object_center
      object_center_gradient object_value_bound object_gradient_bounds
      object_hessian.
    bounded_case16594_object_dispatch_semantic_trace 524405
      (bounded_object_q_cv_list semantic_center_boxes)
      (bounded_object_q_cv_list semantic_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      bounded_case16594_program bounded_case16594_prepared_program
      bounded_case16594_generic_prefix167_codes_cv
      bounded_case16594_generic_prefix167_sources_cv
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packets))
      [] ([],word_certificates)
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list [runtime_state]) (Num 0)))
      ([BoundedObjectQTaylor T object_center object_center_gradient
          object_value_bound object_gradient_bounds object_hessian],[]) /\
    runtime_state =
      bounded_case16594_object_state_cv (Num 1) runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    bounded_packed_object_source_accept6 runtime_radii runtime_center
      runtime_center_gradient runtime_hessian
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `word_center_boxes` |-> `word_center_boxes`,
          `word_outer_boxes` |-> `word_outer_boxes`,
          `word_state` |-> `([],word_certificates)`,
          `final_word_state` |-> `([word_result],[])`,
          `packets` |-> `packets`,
          `semantic_state` |-> `([],word_certificates)`,
          `runtime_stack` |-> `[]`]
         compute_boundedCase16594ObjectDispatchJointCompleteInvariantTheory.bounded_case16594_object_joint_complete_trace)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> simp
           [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
            compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def])
  >> disch_then
       (qx_choose_then `word_after167`
         (qx_choose_then `packets_after167`
           (qx_choose_then `semantic_after167`
             (qx_choose_then `runtime_stack_after167` strip_assume_tac))))
  >> fs
       [compute_boundedCase16594ObjectDispatchJointCompleteInvariantTheory.bounded_case16594_generic_complete_program_identity,
        compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> `bounded_object_q_analytic_run semantic_radii weights
        semantic_center_boxes semantic_outer_boxes bounded_case16594_program
        bounded_case16594_prepared_program ([],word_certificates)
        semantic_after167` by
       metis_tac
         [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_projects_run]
  >> `bounded_analytic64_program_run semantic_radii word_center_boxes
        word_outer_boxes bounded_case16594_prepared_program
        ([],word_certificates) = SOME ([word_result],[])` by
       metis_tac
         [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_projects_run]
  >> `bounded_analytic64_program_eval semantic_radii word_center_boxes
        word_outer_boxes bounded_case16594_prepared_program
        word_certificates = SOME word_result` by
       simp
         [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_def]
  >> `bounded_taylor64_well_formed word_result` by
       metis_tac
         [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some]
  >> PairCases_on `semantic_after167`
  >> Cases_on `semantic_after1670`
  >- gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        LIST_REL_def]
  >> Cases_on `t`
  >> gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        LIST_REL_def]
  >> Cases_on `h`
  >> rename1
       `bounded_taylor64_covers_object_q word_result
          (BoundedObjectQTaylor object_domain object_center
            object_center_gradient object_value_bound object_gradient_bounds
            object_hessian)`
  >> `object_value_bound =
        bounded_object_q_taylor_value_complete_cv object_center
          (bounded_object_q_taylor_error_cv semantic_radii
            object_center_gradient weights object_hessian)` by
       metis_tac
         [compute_boundedCase16594FinalObjectBoundaryTheory.bounded_case16594_object_run_value_complete]
  >> `object_domain /\
        bounded_object_q_interval_upper_strict_negative object_value_bound` by
       metis_tac
         [compute_boundedPackedAnalyticNegativeBoundaryTheory.bounded_packed_analytic_result_accepts_object_q_negative]
  >> `bounded_object_q_ordinary_accept6 object_domain semantic_radii
        object_center object_center_gradient weights object_hessian` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_packed_object_completed_negative_refines_ordinary_accept6]
  >> `bounded_packed_object_source_accept6
        (MAP bounded_word64_object_q_cv semantic_radii)
        object_center object_center_gradient object_hessian` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_object_ordinary_accept_refines_source]
  >> `bounded_object_q_taylor_stack_runtime_refines runtime_stack_after167
        [BoundedObjectQTaylor T object_center object_center_gradient
          object_value_bound object_gradient_bounds object_hessian]` by
       fs []
  >> `?runtime_state.
        runtime_stack_after167 = [runtime_state] /\
        bounded_object_q_taylor_runtime_refines runtime_state
          (BoundedObjectQTaylor T object_center object_center_gradient
            object_value_bound object_gradient_bounds object_hessian)` by
       metis_tac [bounded_object_q_taylor_stack_runtime_refines_singleton_general]
  >> `?runtime_center runtime_center_gradient runtime_value_bound
         runtime_gradient_bounds runtime_hessian.
        runtime_state =
          bounded_case16594_object_state_cv (Num 1) runtime_center
            (bounded_object_q_cv_list runtime_center_gradient)
            runtime_value_bound
            (bounded_object_q_cv_list runtime_gradient_bounds)
            (bounded_object_q_cv_list runtime_hessian) /\
        bounded_packed_object_source_accept6 runtime_radii runtime_center
          runtime_center_gradient runtime_hessian` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimeAcceptTransferTheory.bounded_object_q_taylor_runtime_refines_source_accept6]
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> qexists_tac `object_center`
  >> qexists_tac `object_center_gradient`
  >> qexists_tac `object_value_bound`
  >> qexists_tac `object_gradient_bounds`
  >> qexists_tac `object_hessian`
  >> fs
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

val _ = export_theory ();
