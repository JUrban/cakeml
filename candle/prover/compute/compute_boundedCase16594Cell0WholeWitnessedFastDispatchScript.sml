(*****************************************************************************
 * Exact witnessed fast-evaluator seam for the genuine case-16594 cell-0    *
 * whole call.                                                               *
 *                                                                           *
 * This is a bounded vertical integration test for the generic four-payload *
 * callback framework.  It is deliberately not the production plan-driven  *
 * checker: every payload and the structured result witness are authenticated *
 * against the imported call before the callback can hit.                    *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeWitnessedFastDispatch
Ancestors
  compute_witnessedPayloadListFast
  compute_boundedCase16594Cell0WholeEval
Libs
  bossLib preamble

Definition bounded_case16594_cell0_whole_witnessed_checker_def:
  bounded_case16594_cell0_whole_witnessed_checker witness
      source_descriptor tree_dim tokens encoded_jobs =
    if witness = bounded_case16594_cell0_whole_hol_light_result /\
       source_descriptor = bounded_case16594_cell0_whole_source_descriptor /\
       tree_dim = bounded_case16594_cell0_whole_tree_dim /\
       tokens = bounded_case16594_cell0_whole_tokens /\
       encoded_jobs = bounded_case16594_cell0_whole_encoded_jobs
    then SOME witness
    else NONE
End

Definition bounded_case16594_cell0_whole_witnessed_list_checker_def:
  bounded_case16594_cell0_whole_witnessed_list_checker =
    compute_witnessed_payload4_list_checker
      bounded_case16594_cell0_whole_witnessed_checker
End

Theorem bounded_case16594_cell0_whole_witnessed_checker_refines:
  compute_witnessed_payloads_refines
    bounded_case16594_cell0_whole_combined_ceqs
    «candle_cv_q_packed_object_whole_check»
    bounded_case16594_cell0_whole_witnessed_list_checker
Proof
  rw
    [compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_refines_def,
     bounded_case16594_cell0_whole_witnessed_list_checker_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payload4_list_checker_def,
     bounded_case16594_cell0_whole_witnessed_checker_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_payloadListFastTheory.compute_literal_call_payloads_sound
  >> gvs []
  >> once_rewrite_tac
       [GSYM
          compute_boundedCase16594Cell0WholePayloadsTheory.bounded_case16594_cell0_whole_entry_from_payloads]
  >> irule
       compute_boundedCase16594Cell0WholeEvalTheory.bounded_case16594_cell0_whole_eval_clock
  >> simp
       [compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_runtime_cell0_codes_cv_length,
        computeTheory.compute_default_clock]
QED

Definition bounded_case16594_cell0_whole_witnessed_fast_eval_def:
  bounded_case16594_cell0_whole_witnessed_fast_eval =
    compute_witnessed_payloads_fast_eval
      bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_nl_certificate_witness»
      «candle_cv_q_packed_object_whole_check»
      bounded_case16594_cell0_whole_witnessed_list_checker
End

Theorem bounded_case16594_cell0_whole_witnessed_fast_eval_ok:
  compute_fast_eval_ok bounded_case16594_cell0_whole_witnessed_fast_eval
Proof
  rw [bounded_case16594_cell0_whole_witnessed_fast_eval_def]
  >> irule
       compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_ok
  >> ACCEPT_TAC bounded_case16594_cell0_whole_witnessed_checker_refines
QED

Theorem bounded_case16594_cell0_whole_witnessed_fast_eval_hit:
  bounded_case16594_cell0_whole_witnessed_fast_eval
    bounded_case16594_cell0_whole_combined_ceqs
    (Let «candle_cv_nl_certificate_witness»
      (from_cv bounded_case16594_cell0_whole_hol_light_result)
      bounded_case16594_cell0_whole_hol_light_entry) =
    SOME bounded_case16594_cell0_whole_hol_light_result
Proof
  simp
    [bounded_case16594_cell0_whole_witnessed_fast_eval_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_def,
     compute_witnessedPayloadListFastTheory.compute_literal_witnessed_payloads_def,
     compute_payloadListFastTheory.compute_literal_call_payloads_def,
     compute_payloadListFastTheory.compute_literal_payloads_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     compute_boundedCase16594Cell0WholePayloadsTheory.bounded_case16594_cell0_whole_entry_from_payloads,
     bounded_case16594_cell0_whole_witnessed_list_checker_def,
     bounded_case16594_cell0_whole_witnessed_checker_def]
QED

Theorem bounded_case16594_cell0_whole_witnessed_fast_eval_rejects_ceqs:
  ceqs <> bounded_case16594_cell0_whole_combined_ceqs ==>
  bounded_case16594_cell0_whole_witnessed_fast_eval ceqs expression = NONE
Proof
  simp
    [bounded_case16594_cell0_whole_witnessed_fast_eval_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_def]
QED

Theorem bounded_case16594_cell0_whole_witnessed_checker_rejects_payload_mutation:
  source_descriptor <> bounded_case16594_cell0_whole_source_descriptor \/
  tree_dim <> bounded_case16594_cell0_whole_tree_dim \/
  token_stream <> bounded_case16594_cell0_whole_tokens \/
  encoded_jobs <> bounded_case16594_cell0_whole_encoded_jobs ==>
  bounded_case16594_cell0_whole_witnessed_checker witness
    source_descriptor tree_dim token_stream encoded_jobs = NONE
Proof
  simp [bounded_case16594_cell0_whole_witnessed_checker_def]
QED

Theorem bounded_case16594_cell0_whole_witnessed_checker_rejects_result_mutation:
  witness <> bounded_case16594_cell0_whole_hol_light_result ==>
  bounded_case16594_cell0_whole_witnessed_checker witness
    source_descriptor tree_dim token_stream encoded_jobs = NONE
Proof
  simp [bounded_case16594_cell0_whole_witnessed_checker_def]
QED

val _ = export_theory ();
