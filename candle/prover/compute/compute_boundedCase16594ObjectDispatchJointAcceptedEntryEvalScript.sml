(*****************************************************************************
 * Generic accepted-cell evaluator endpoint for the case-16594 object entry.
 *
 * The fixed-word checker remains the untrusted witness producer.  If its
 * complete trace, packet contracts, and final packed verdict succeed, the
 * joint semantic theorem supplies the exact production object result.  This
 * theory connects that result through the actual dispatcher-program and
 * dispatcher-entry evaluators.  No genuine-cell constants occur here.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointAcceptedEntryEval
Ancestors
  compute_boundedCase16594ObjectDispatchJointAcceptedInvariant
  compute_boundedCase16594ObjectDispatchEntryControlEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_joint_complete_runtime_payload_identity:
  bounded_case16594_generic_prefix167_codes_cv =
    bounded_case16594_dispatch_codes_cv /\
  bounded_case16594_generic_prefix167_sources_cv =
    bounded_case16594_source_program_cv
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_joint_complete_accepted_entry_eval:
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
  bounded_packed_analytic_result_accepts word_result /\
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 3 < clock
  ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv (bounded_object_q_cv_list semantic_center_boxes);
       from_cv (bounded_object_q_cv_list semantic_outer_boxes);
       from_cv (bounded_object_q_cv_list runtime_radii);
       from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_object_q_cv_list
           (MAP bounded_interval64_object_q_cv packets))])
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
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
          `word_certificates` |-> `word_certificates`,
          `word_result` |-> `word_result`, `packets` |-> `packets`]
         compute_boundedCase16594ObjectDispatchJointAcceptedInvariantTheory.bounded_case16594_object_joint_complete_accepted_runtime_state)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `runtime_state`
         (qx_choose_then `runtime_center`
           (qx_choose_then `runtime_center_gradient`
             (qx_choose_then `runtime_value_bound`
               (qx_choose_then `runtime_gradient_bounds`
                 (qx_choose_then `runtime_hessian`
                   (qx_choose_then `object_center`
                     (qx_choose_then `object_center_gradient`
                       (qx_choose_then `object_value_bound`
                         (qx_choose_then `object_gradient_bounds`
                           (qx_choose_then `object_hessian`
                             strip_assume_tac)))))))))))
  >> `compute_eval (clock - 1)
        bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_dispatch_program»
          [from_cv (bounded_object_q_cv_list semantic_center_boxes);
           from_cv (bounded_object_q_cv_list semantic_outer_boxes);
           from_cv (bounded_object_q_cv_list runtime_radii);
           from_cv bounded_case16594_generic_prefix167_codes_cv;
           from_cv bounded_case16594_generic_prefix167_sources_cv;
           from_cv
             (bounded_object_q_cv_list
               (MAP bounded_interval64_object_q_cv packets));
           from_cv (bounded_object_q_cv_list [])]) refs =
        (M_success
          (from_cv
            (Pair (Num 1)
              (Pair (bounded_object_q_cv_list [runtime_state]) (Num 0)))),
         refs)` by
       (irule
          compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_eval
        >> qexists_tac
             `([BoundedObjectQTaylor T object_center
                  object_center_gradient object_value_bound
                  object_gradient_bounds object_hessian],[])`
        >> qexists_tac `bounded_case16594_prepared_program`
        >> qexists_tac `semantic_center_boxes`
        >> qexists_tac `semantic_outer_boxes`
        >> qexists_tac `semantic_radii`
        >> qexists_tac `([],word_certificates)`
        >> qexists_tac `bounded_case16594_program`
        >> qexists_tac `524405`
        >> qexists_tac `weights`
        >> asm_rewrite_tac []
        >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDispatchEntryControlEvalTheory.bounded_case16594_object_dispatch_entry_from_program_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_center`
  >> qexists_tac `bounded_object_q_cv_list runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> qexists_tac `runtime_value_bound`
  >> asm_rewrite_tac []
  >> fs
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
