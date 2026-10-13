(*****************************************************************************
 * Production evaluator chain for the first genuine specialized NL packet.
 *
 * A successful authenticated packet check is consumed directly.  A miss or
 * rejection delegates to the existing proved pure evaluator, which in turn
 * retains compute_with's verified evaluator fallback.
 *****************************************************************************)
Theory compute_packetFastChain
Ancestors
  compute_fastChain compute_registeredCase10173PacketFast
Libs
  bossLib preamble

Definition compute_case10173_packet_fast_eval_def:
  compute_case10173_packet_fast_eval =
    compute_fast_eval_chain
      registered_case10173_cell0_packet_fast_eval
      compute_pure_fast_eval
End

Theorem compute_case10173_packet_fast_eval_ok:
  compute_fast_eval_ok compute_case10173_packet_fast_eval
Proof
  rw [compute_case10173_packet_fast_eval_def]
  >> irule compute_fast_eval_chain_ok
  >> simp
       [compute_registeredCase10173PacketFastTheory.registered_case10173_cell0_packet_fast_eval_ok,
        compute_pureFastTheory.compute_pure_fast_eval_ok]
QED

Definition compute_case10173_packet_fast_def:
  compute_case10173_packet_fast (ths,ceqs) tm =
    compute_with compute_case10173_packet_fast_eval (ths,ceqs) tm
End

Theorem compute_case10173_packet_fast_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_case10173_packet_fast (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_case10173_packet_fast_def]
  >> strip_tac
  >> assume_tac compute_case10173_packet_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `compute_case10173_packet_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
