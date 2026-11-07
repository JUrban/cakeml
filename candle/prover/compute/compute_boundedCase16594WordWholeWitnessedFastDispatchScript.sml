(*****************************************************************************
 * Witnessed fast-evaluator dispatch for the complete case-16594 whole call. *
 *                                                                           *
 * The otherwise-unused Let witness contains the external fixed-word         *
 * certificate.  All four ordinary call payloads remain runtime inputs and   *
 * are authenticated by the complete checker before a fast result can hit.   *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeWitnessedFastDispatch
Ancestors
  compute_witnessedPayloadListFast
  compute_boundedCase16594WordWholeChecker
Libs
  bossLib preamble

Definition bounded_case16594_word_whole_witnessed_list_checker_def:
  bounded_case16594_word_whole_witnessed_list_checker =
    compute_witnessed_payload4_list_checker
      bounded_case16594_word_whole_checker
End

Theorem bounded_case16594_word_whole_default_clock_capacity:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 875 + 20 <
      compute_default_clock - 1 /\
  bounded_case16594_word_topology_fuel + 20 < compute_default_clock - 1
Proof
  rw
    [compute_boundedCase16594WordWholeCheckerTheory.bounded_case16594_word_topology_fuel_def,
     compute_boundedCase16594ObjectDispatchJointAcceptedEntryEvalTheory.bounded_case16594_object_joint_complete_runtime_payload_identity,
     GSYM
       compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_codes_identity,
     compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_runtime_cell0_codes_cv_length,
     computeTheory.compute_default_clock]
QED

Theorem bounded_case16594_word_whole_witnessed_checker_refines:
  compute_witnessed_payloads_refines
    bounded_case16594_cell0_whole_combined_ceqs
    «candle_cv_q_packed_object_whole_check»
    bounded_case16594_word_whole_witnessed_list_checker
Proof
  rw
    [compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_refines_def,
     bounded_case16594_word_whole_witnessed_list_checker_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payload4_list_checker_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_payloadListFastTheory.compute_literal_call_payloads_sound
  >> gvs []
  >> irule
       compute_boundedCase16594WordWholeCheckerTheory.bounded_case16594_word_whole_checker_eval_clock
  >> asm_rewrite_tac
       [bounded_case16594_word_whole_default_clock_capacity]
  >> qexists_tac `witness`
  >> asm_rewrite_tac []
QED

Definition bounded_case16594_word_whole_witnessed_fast_eval_def:
  bounded_case16594_word_whole_witnessed_fast_eval =
    compute_witnessed_payloads_fast_eval
      bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_nl_certificate_witness»
      «candle_cv_q_packed_object_whole_check»
      bounded_case16594_word_whole_witnessed_list_checker
End

Theorem bounded_case16594_word_whole_witnessed_fast_eval_ok:
  compute_fast_eval_ok bounded_case16594_word_whole_witnessed_fast_eval
Proof
  rw [bounded_case16594_word_whole_witnessed_fast_eval_def]
  >> irule
       compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_ok
  >> ACCEPT_TAC bounded_case16594_word_whole_witnessed_checker_refines
QED

Theorem bounded_case16594_word_whole_witnessed_fast_eval_rejects_ceqs:
  ceqs <> bounded_case16594_cell0_whole_combined_ceqs ==>
  bounded_case16594_word_whole_witnessed_fast_eval ceqs expression = NONE
Proof
  simp
    [bounded_case16594_word_whole_witnessed_fast_eval_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_def]
QED

val _ = export_theory ();
