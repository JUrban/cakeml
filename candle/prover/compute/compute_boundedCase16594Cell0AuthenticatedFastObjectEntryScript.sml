(*****************************************************************************
 * Exact accepted entry for the authenticated genuine case-16594 cell 0.
 *
 * The entry deliberately embeds the checked fast certificate stream.  That
 * stream is distinct from the legacy certificate field of the older exported
 * entry, so this theory gives the fast payload its own exact cexp identity.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedFastObjectEntry
Ancestors
  compute_boundedCase16594ObjectDispatchEntryControlEval
Libs
  bossLib preamble wordsLib intLib

Definition bounded_case16594_cell0_authenticated_fast_object_entry_cexp_def:
  bounded_case16594_cell0_authenticated_fast_object_entry_cexp =
    App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv bounded_case16594_runtime_cell0_center_boxes_cv;
       from_cv bounded_case16594_runtime_cell0_outer_boxes_cv;
       from_cv
         (bounded_object_q_cv_list
           bounded_case16594_cell0_authenticated_object_radii);
       from_cv bounded_case16594_runtime_cell0_codes_cv;
       from_cv bounded_case16594_runtime_cell0_sources_cv;
       from_cv bounded_case16594_cell0_fast_object_certificates_cv]
End

Theorem bounded_case16594_cell0_authenticated_object_accepted_program_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 2 < clock ==>
  ?runtime_state runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
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
  strip_tac
  >> mp_tac
       compute_boundedCase16594Cell0AuthenticatedObjectAcceptanceTheory.bounded_case16594_cell0_authenticated_object_semantic_accept
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
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectAcceptanceTheory.bounded_object_q_taylor_stack_runtime_refines_singleton]
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
  >> `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
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
        >> metis_tac [])
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

Theorem bounded_case16594_cell0_authenticated_fast_object_entry_eval:
  compute_eval compute_default_clock
    bounded_case16594_object_dispatch_cell0_ceqs
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp
    (refs:hol_refs) =
  (M_success (from_cv (Num 1)),refs)
Proof
  mp_tac
    (Q.INST [`clock` |-> `compute_default_clock - 1`]
      bounded_case16594_cell0_authenticated_object_accepted_program_eval_clock)
  >> impl_tac
  >- simp
       [compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_runtime_cell0_codes_cv_length,
        computeTheory.compute_default_clock]
  >> disch_then
       (qx_choose_then `runtime_state`
         (qx_choose_then `runtime_center`
           (qx_choose_then `runtime_center_gradient`
             (qx_choose_then `runtime_value_bound`
               (qx_choose_then `runtime_gradient_bounds`
                 (qx_choose_then `runtime_hessian` strip_assume_tac))))))
  >> rw
       [bounded_case16594_cell0_authenticated_fast_object_entry_cexp_def]
  >> irule EQ_TRANS
  >> qexists_tac `(M_success (from_cv (Num 1)),refs)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchEntryControlEvalTheory.bounded_case16594_object_dispatch_entry_from_program_eval
      >> conj_tac
      >- simp [computeTheory.compute_default_clock]
      >> qexists_tac `runtime_center_gradient`
      >> qexists_tac `runtime_center`
      >> qexists_tac `bounded_object_q_cv_list runtime_gradient_bounds`
      >> qexists_tac `runtime_hessian`
      >> qexists_tac `runtime_value_bound`
      >> simp
           [compute_boundedCase16594Cell0RuntimePayloadIdentityTheory.bounded_case16594_cell0_authenticated_radii_payload_identity]
      >> fs [compute_execTheory.from_cv_def])
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
