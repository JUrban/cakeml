(*****************************************************************************
 * Authenticated fast-certificate payload for genuine case-16594 cell 0.
 *
 * The fixed-word trace emits 134 interval witnesses.  The production object
 * dispatcher consumes the exact object-q image of those intervals.  Keep
 * this payload distinct from the legacy rational certificate field in the
 * older cell-0 entry: the two lists have the same length but different
 * representations and must never be substituted for one another silently.
 *****************************************************************************)
Theory compute_boundedCase16594Cell0FastCertificatePayload
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594ObjectDispatchCell0PayloadIdentity
  compute_boundedCase16594ObjectDispatchProgramTraceEval
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_cell0_fast_object_certificates_def:
  bounded_case16594_cell0_fast_object_certificates =
    MAP bounded_interval64_object_q_cv
      bounded_case16594_cell0_authenticated_word_runtime_packets
End

Definition bounded_case16594_cell0_fast_object_certificates_cv_def:
  bounded_case16594_cell0_fast_object_certificates_cv =
    bounded_object_q_cv_list
      bounded_case16594_cell0_fast_object_certificates
End

Theorem bounded_case16594_object_cv_list_length_encode:
  !items.
    bounded_case16594_object_cv_list_length
      (bounded_object_q_cv_list items) = LENGTH items
Proof
  Induct
  >> simp
       [compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_cv_list_length_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

Theorem bounded_case16594_cell0_fast_object_certificates_length:
  LENGTH bounded_case16594_cell0_fast_object_certificates = 134 /\
  bounded_case16594_object_cv_list_length
    bounded_case16594_cell0_fast_object_certificates_cv = 134
Proof
  simp
    [bounded_case16594_cell0_fast_object_certificates_def,
     bounded_case16594_cell0_fast_object_certificates_cv_def,
     bounded_case16594_object_cv_list_length_encode,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_trace_exact]
QED

Theorem bounded_case16594_cell0_legacy_certificate_payload_distinct:
  bounded_case16594_runtime_cell0_certificates_cv <>
    bounded_case16594_cell0_fast_object_certificates_cv
Proof
  simp
    [compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_certificates_cv_def,
     bounded_case16594_cell0_fast_object_certificates_cv_def,
     bounded_case16594_cell0_fast_object_certificates_def,
     compute_boundedCase16594Cell0AuthenticatedWordRuntimeTraceTheory.bounded_case16594_cell0_authenticated_word_runtime_packets_def,
     compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_object_q_cv_def,
     compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_signed64_object_q_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
QED

val _ = export_theory ();
