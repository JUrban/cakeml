(*****************************************************************************
 * Genuine canonical-packet fast-evaluator seam.
 *
 * This is the smallest proof-producing test of the production mechanism:
 * authenticate the exact registered equation/call identity, execute the
 * fail-closed packet checker, and return the existing canonical result only
 * when the checker accepts.  The refinement theorem makes the result usable
 * by compute_with without replaying the generic evaluator at run time.
 *****************************************************************************)
Theory compute_registeredCase10173PacketFast
Ancestors
  compute_registeredCase10173Cell0Fast
  compute_boundedCase10173Packet
Libs
  bossLib preamble

Definition registered_case10173_cell0_packet_fast_eval_def:
  registered_case10173_cell0_packet_fast_eval ceqs cexp =
    if ceqs = registered_case10173_cell0_ceqs /\
       cexp = registered_case10173_cell0_cexp
    then
      case bounded_case10173_packet_check_cv
        (bounded_cv_encode_case10173_packet
          bounded_case10173_cell0_packet) of
      | SOME (Num 1) => SOME registered_case10173_cell0_result
      | _ => NONE
    else NONE
End

Theorem registered_case10173_cell0_packet_fast_eval_hit:
  registered_case10173_cell0_packet_fast_eval
    registered_case10173_cell0_ceqs registered_case10173_cell0_cexp =
  SOME registered_case10173_cell0_result
Proof
  simp [registered_case10173_cell0_packet_fast_eval_def,
        bounded_case10173_cell0_packet_check_cv]
QED

Theorem registered_case10173_cell0_packet_fast_eval_ok:
  compute_fast_eval_ok registered_case10173_cell0_packet_fast_eval
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      registered_case10173_cell0_packet_fast_eval_def]
  >> every_case_tac
  >> gvs [bounded_case10173_cell0_packet_check_cv,
          compute_registeredCase10173Cell0FastTheory.registered_case10173_cell0_compute_eval]
QED

Definition compute_registered_case10173_cell0_packet_fast_def:
  compute_registered_case10173_cell0_packet_fast (ths,ceqs) tm =
    compute_with registered_case10173_cell0_packet_fast_eval (ths,ceqs) tm
End

Theorem compute_registered_case10173_cell0_packet_fast_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_registered_case10173_cell0_packet_fast (ths,ceqs) tm s =
    (res,s') ==>
  s' = s /\
  (!th. res = M_success th ==> THM ctxt th) /\
  (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_registered_case10173_cell0_packet_fast_def]
  >> strip_tac
  >> assume_tac registered_case10173_cell0_packet_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `registered_case10173_cell0_packet_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
