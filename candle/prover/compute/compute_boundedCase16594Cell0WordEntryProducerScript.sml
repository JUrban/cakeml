(*****************************************************************************
 * Genuine cell-0 equality test for the generic fixed-word entry producer.
 *
 * This is the bounded production-shape probe: the 31 typed certificates are
 * the inputs, and the producer must return exactly the independently imported
 * 134-packet object-q payload already used by the ordinary HOL Light call.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WordEntryProducer
Ancestors
  compute_boundedCase16594WordEntryProducer
  compute_boundedCase16594Cell0FastCertificatePayload
  compute_boundedCase16594Cell0AuthenticatedWordObjectBridge
Libs
  bossLib preamble wordsLib

Theorem bounded_case16594_cell0_word_entry_inputs_valid:
  LENGTH bounded_case16594_cell0_source_word_radii = 6 /\
  LENGTH bounded_case16594_cell0_source_word_center_environment = 6 /\
  LENGTH bounded_case16594_cell0_authenticated_word_box_environment = 6 /\
  EVERY bounded_interval64_valid
    bounded_case16594_cell0_source_word_center_environment /\
  EVERY bounded_interval64_valid
    bounded_case16594_cell0_authenticated_word_box_environment
Proof
  rw
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_radii_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_environment_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_environment_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_cell0_word_entry_trace:
  bounded_analytic64_program_runtime_certificate_trace
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_prepared_program
      ([],bounded_case16594_cell0_source_word_certificates) =
    SOME
      (([bounded_case16594_cell0_authenticated_word_result],[]),
       bounded_case16594_cell0_authenticated_word_runtime_packets)
Proof
  rw
    [compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_radii_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_center_environment_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_box_environment_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_source_word_certificates_def,
     GSYM
       compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_trace_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_trace_exact,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_final_state_shape]
QED

Theorem bounded_case16594_cell0_word_entry_produce_exact:
  bounded_case16594_word_entry_produce
      bounded_case16594_cell0_source_word_radii
      bounded_case16594_cell0_source_word_center_environment
      bounded_case16594_cell0_authenticated_word_box_environment
      bounded_case16594_cell0_source_word_certificates =
    SOME bounded_case16594_cell0_fast_object_certificates_cv
Proof
  rw
    [compute_boundedCase16594WordEntryProducerTheory.bounded_case16594_word_entry_produce_def,
     bounded_case16594_cell0_word_entry_inputs_valid,
     compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_radius_pairs,
     bounded_case16594_cell0_word_entry_trace,
     compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_cell0_word_dispatch_packet_contracts,
     compute_boundedCase16594Cell0AuthenticatedWordObjectBridgeTheory.bounded_case16594_cell0_authenticated_word_result_accepts,
     compute_boundedCase16594Cell0FastCertificatePayloadTheory.bounded_case16594_cell0_fast_object_certificates_cv_def,
     compute_boundedCase16594Cell0FastCertificatePayloadTheory.bounded_case16594_cell0_fast_object_certificates_def]
QED

val _ = export_theory ();
