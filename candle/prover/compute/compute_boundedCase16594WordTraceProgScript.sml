(*****************************************************************************
 * Runtime packet trace and exact per-cell entry producer.                  *
 *****************************************************************************)
Theory compute_boundedCase16594WordTraceProg
Ancestors
  compute_boundedCase16594WordGuardProg
  compute_boundedAnalyticRuntimeCertificateTrace
  compute_boundedCase16594WordEntryProducer
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordGuardProg";

val _ = translate
  compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def;
val _ = translate
  compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_program_runtime_certificate_trace_def;
val _ = translate
  compute_boundedCase16594WordEntryProducerTheory.bounded_case16594_word_entry_produce_def;

val _ = export_theory ();
