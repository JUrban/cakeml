(*****************************************************************************
 * Witnessed fast-evaluator dispatch for the complete direct case-16594 call. *
 *                                                                           *
 * The direct topology refinement has a clock bound proportional to the      *
 * runtime token stream.  The fast seam therefore admits only the genuine    *
 * case-16594 dimension and an upper bound equal to its complete 1,749-token  *
 * topology.  Inputs outside that bounded domain return NONE and retain the   *
 * ordinary compute path.                                                     *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectWitnessedFastDispatch
Ancestors
  compute_witnessedPayloadListFast
  compute_boundedCase16594WordWholeDirectChecker
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_whole_direct_bounded_checker_def:
  bounded_case16594_word_whole_direct_bounded_checker certificate
      source_descriptor tree_dim token_stream encoded_jobs =
    if tree_dim = Num 6 /\
       bounded_case16594_direct_cv_list_length token_stream <= 1749
    then
      bounded_case16594_word_whole_direct_checker certificate
        source_descriptor tree_dim token_stream encoded_jobs
    else NONE
End

Definition bounded_case16594_word_whole_direct_witnessed_list_checker_def:
  bounded_case16594_word_whole_direct_witnessed_list_checker =
    compute_witnessed_payload4_list_checker
      bounded_case16594_word_whole_direct_bounded_checker
End

Theorem bounded_case16594_word_whole_direct_default_clock_capacity:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 875 + 20 <
      compute_default_clock - 1 /\
  1749 * (6 + 42) + 20 < compute_default_clock - 1
Proof
  rw
    [compute_boundedCase16594ObjectDispatchJointAcceptedEntryEvalTheory.bounded_case16594_object_joint_complete_runtime_payload_identity,
     GSYM
       compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_codes_identity,
     compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_runtime_cell0_codes_cv_length,
     computeTheory.compute_default_clock]
QED

Theorem bounded_case16594_word_whole_direct_witnessed_checker_refines:
  compute_witnessed_payloads_refines
    bounded_case16594_cell0_whole_combined_ceqs
    «candle_cv_q_packed_object_whole_check»
    bounded_case16594_word_whole_direct_witnessed_list_checker
Proof
  rw
    [compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_refines_def,
     bounded_case16594_word_whole_direct_witnessed_list_checker_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payload4_list_checker_def,
     bounded_case16594_word_whole_direct_bounded_checker_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_payloadListFastTheory.compute_literal_call_payloads_sound
  >> gvs []
  >> irule
       (PURE_REWRITE_RULE [compute_execTheory.from_cv_def]
          compute_boundedCase16594WordWholeDirectCheckerTheory.bounded_case16594_word_whole_direct_checker_eval_clock)
  >> conj_tac
  >- (assume_tac
        (CONJUNCT2
          bounded_case16594_word_whole_direct_default_clock_capacity)
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- ACCEPT_TAC
       (CONJUNCT1
          bounded_case16594_word_whole_direct_default_clock_capacity)
  >> qexists_tac `witness`
  >> asm_rewrite_tac []
QED

Definition bounded_case16594_word_whole_direct_witnessed_fast_eval_def:
  bounded_case16594_word_whole_direct_witnessed_fast_eval =
    compute_witnessed_payloads_fast_eval
      bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_nl_certificate_witness»
      «candle_cv_q_packed_object_whole_check»
      bounded_case16594_word_whole_direct_witnessed_list_checker
End

Theorem bounded_case16594_word_whole_direct_witnessed_fast_eval_ok:
  compute_fast_eval_ok
    bounded_case16594_word_whole_direct_witnessed_fast_eval
Proof
  rw [bounded_case16594_word_whole_direct_witnessed_fast_eval_def]
  >> irule
       compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_ok
  >> ACCEPT_TAC
       bounded_case16594_word_whole_direct_witnessed_checker_refines
QED

Theorem bounded_case16594_word_whole_direct_witnessed_fast_eval_rejects_ceqs:
  ceqs <> bounded_case16594_cell0_whole_combined_ceqs ==>
  bounded_case16594_word_whole_direct_witnessed_fast_eval ceqs expression =
    NONE
Proof
  simp
    [bounded_case16594_word_whole_direct_witnessed_fast_eval_def,
     compute_witnessedPayloadListFastTheory.compute_witnessed_payloads_fast_eval_def]
QED

Theorem bounded_case16594_word_whole_direct_bounded_checker_rejects_dimension:
  tree_dim <> Num 6 ==>
  bounded_case16594_word_whole_direct_bounded_checker certificate
    source_descriptor tree_dim token_stream encoded_jobs = NONE
Proof
  simp [bounded_case16594_word_whole_direct_bounded_checker_def]
QED

Theorem bounded_case16594_word_whole_direct_bounded_checker_rejects_long_topology:
  1749 < bounded_case16594_direct_cv_list_length token_stream ==>
  bounded_case16594_word_whole_direct_bounded_checker certificate
    source_descriptor tree_dim token_stream encoded_jobs = NONE
Proof
  simp [bounded_case16594_word_whole_direct_bounded_checker_def]
QED

val _ = export_theory ();
