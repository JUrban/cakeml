(*****************************************************************************
 * Production evaluator chain with the complete genuine case-10173 stream.
 *
 * The authenticated full-stream branch is tried first.  Any different
 * equation environment, entry point, payload, or rejected certificate falls
 * through unchanged to the existing packet and general pure evaluators.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineFastChain
Ancestors
  compute_packetFastChain
  compute_registeredCase10173GenuineAuthenticatedFast
Libs
  bossLib preamble

Definition compute_case10173_genuine_fast_eval_def:
  compute_case10173_genuine_fast_eval =
    compute_fast_eval_chain
      registered_case10173_genuine_decimal_authenticated_fast_eval
      compute_case10173_packet_fast_eval
End

Theorem compute_case10173_genuine_fast_eval_ok:
  compute_fast_eval_ok compute_case10173_genuine_fast_eval
Proof
  rw [compute_case10173_genuine_fast_eval_def]
  >> irule compute_fastChainTheory.compute_fast_eval_chain_ok
  >> simp
       [compute_registeredCase10173GenuineAuthenticatedFastTheory.registered_case10173_genuine_decimal_authenticated_fast_eval_ok,
        compute_packetFastChainTheory.compute_case10173_packet_fast_eval_ok]
QED

Definition compute_case10173_genuine_fast_def:
  compute_case10173_genuine_fast (ths,ceqs) tm =
    compute_with compute_case10173_genuine_fast_eval (ths,ceqs) tm
End

Theorem compute_case10173_genuine_fast_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_case10173_genuine_fast (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_case10173_genuine_fast_def]
  >> strip_tac
  >> assume_tac compute_case10173_genuine_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `compute_case10173_genuine_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
