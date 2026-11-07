(*****************************************************************************
 * Pure atan and packet-ledger guards for the exact word certificate.       *
 *****************************************************************************)
Theory compute_boundedCase16594WordGuardProg
Ancestors
  compute_boundedCase16594WordRuntimeBaseProg
  compute_boundedCase16594ObjectCertifiedAtanDispatchInvariant
  compute_boundedCase16594Cell0WordDispatchPacketContracts
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordRuntimeBaseProg";

val _ = translate
  compute_boundedCase16594ObjectCertifiedAtanDispatchInvariantTheory.bounded_case16594_object_atan_fixed_pure_contract_def;
val _ = translate
  compute_boundedCase16594Cell0WordDispatchPacketContractsTheory.bounded_case16594_word_dispatch_packet_contracts_def;

val _ = export_theory ();
