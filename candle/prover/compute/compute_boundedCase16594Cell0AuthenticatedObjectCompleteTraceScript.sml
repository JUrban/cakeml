(*****************************************************************************
 * Complete genuine-cell trace, normalized to the production 167-step plan.
 *
 * The fast object certificate stream is deliberately named explicitly.  It
 * is not the distinct legacy certificate payload in the older exported entry.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedObjectCompleteTrace
Ancestors
  compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTrace
  compute_boundedCase16594Cell0FastCertificatePayload
  compute_boundedCase16594ObjectDispatchCell0TraceContract
Libs
  bossLib preamble wordsLib intLib

Theorem bounded_case16594_cell0_complete_trace_payload_identities:
  bounded_case16594_source_prefix167 = bounded_case16594_program /\
  bounded_case16594_prepared_prefix167 =
    bounded_case16594_prepared_program /\
  bounded_case16594_prefix167_codes_cv =
    bounded_case16594_runtime_cell0_codes_cv /\
  bounded_case16594_prefix167_sources_cv =
    bounded_case16594_runtime_cell0_sources_cv /\
  bounded_case16594_authenticated_fast_packets_cv =
    bounded_case16594_cell0_fast_object_certificates_cv /\
  bounded_case16594_prepared_suffix_after167 = []
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTraceTheory.bounded_case16594_source_prefix167_def,
     compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTraceTheory.bounded_case16594_prepared_prefix167_def,
     compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTraceTheory.bounded_case16594_prefix167_codes_cv_def,
     compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTraceTheory.bounded_case16594_prefix167_sources_cv_def,
     compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTraceTheory.bounded_case16594_prepared_suffix_after167_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdSpecializedPairTraceTheory.bounded_case16594_source_prefix122_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdSpecializedPairTraceTheory.bounded_case16594_prepared_prefix122_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdSpecializedPairTraceTheory.bounded_case16594_prefix122_codes_cv_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdSpecializedPairTraceTheory.bounded_case16594_prefix122_sources_cv_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTraceTheory.bounded_case16594_source_prefix120_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTraceTheory.bounded_case16594_prepared_prefix120_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTraceTheory.bounded_case16594_prefix120_codes_cv_def,
     compute_boundedCase16594Cell0AuthenticatedObjectThirdOrdinaryStretchTraceTheory.bounded_case16594_prefix120_sources_cv_def,
     compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_codes_identity,
     compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_sources_identity,
     compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_authenticated_fast_packets_cv_def,
     compute_boundedCase16594Cell0FastCertificatePayloadTheory.bounded_case16594_cell0_fast_object_certificates_cv_def,
     compute_boundedCase16594Cell0FastCertificatePayloadTheory.bounded_case16594_cell0_fast_object_certificates_def]
  >> EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_cell0_authenticated_object_complete_trace:
  ?semantic_after runtime_stack_after.
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
        (Pair (bounded_object_q_cv_list runtime_stack_after) (Num 0)))
      semantic_after /\
    bounded_analytic64_state_covers_object_q
      bounded_case16594_cell0_authenticated_word_runtime_final_state
      semantic_after /\
    bounded_case16594_word_dispatch_packet_contracts
      (SND bounded_case16594_cell0_authenticated_word_runtime_final_state) []
Proof
  mp_tac
    compute_boundedCase16594Cell0AuthenticatedObjectFinalOrdinaryTailTraceTheory.bounded_case16594_cell0_authenticated_object_prefix0_through166_trace
  >> disch_then
       (qx_choose_then `word_after`
         (qx_choose_then `packets_after`
           (qx_choose_then `semantic_after`
             (qx_choose_then `runtime_stack_after` strip_assume_tac))))
  >> fs
       [bounded_case16594_cell0_complete_trace_payload_identities,
        compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_final_state_shape,
        compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> gvs []
  >> fs
       [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> qexists_tac `semantic_after`
  >> qexists_tac `runtime_stack_after`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_cell0_authenticated_object_program_eval:
  ?semantic_after runtime_stack_after.
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
            (Pair (bounded_object_q_cv_list runtime_stack_after) (Num 0)))),
       refs) /\
    bounded_analytic64_state_covers_object_q
      bounded_case16594_cell0_authenticated_word_runtime_final_state
      semantic_after
Proof
  mp_tac bounded_case16594_cell0_authenticated_object_complete_trace
  >> strip_tac
  >> qexists_tac `semantic_after`
  >> qexists_tac `runtime_stack_after`
  >> asm_rewrite_tac []
  >> `(Num 0:cv) = bounded_object_q_cv_list []` by
       simp
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> PURE_REWRITE_TAC [ASSUME ``(Num 0:cv) = bounded_object_q_cv_list []``]
  >> irule
       compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_eval
  >> metis_tac
       [compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_object_dispatch_cell0_default_clock_capacity]
QED

val _ = export_theory ();
