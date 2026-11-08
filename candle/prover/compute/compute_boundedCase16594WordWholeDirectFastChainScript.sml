(*****************************************************************************
 * Production evaluator chain with the complete direct case-16594 callback. *
 *                                                                           *
 * The exact case-16594 branch is tried first.  A different equation         *
 * environment, witness, payload, dimension, overlong topology, or rejected *
 * certificate returns NONE and falls through unchanged to the existing     *
 * generic proved evaluator.  The newer case-10173 tag-10 fast path         *
 * can be reintroduced after the two independently proved artifact graphs   *
 * have been coherently relinked; it is not needed for case 16594 and every  *
 * miss still falls through to the ordinary sound evaluator.                *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectFastChain
Ancestors
  compute_boundedCase16594WordWholeDirectWitnessedFastDispatch
  compute_pureFast
  computeProof
Libs
  bossLib preamble

Definition compute_case16594_direct_genuine_fast_eval_def:
  compute_case16594_direct_genuine_fast_eval ceqs expression =
    case bounded_case16594_word_whole_direct_witnessed_fast_eval
        ceqs expression of
    | SOME result => SOME result
    | NONE => compute_pure_fast_eval ceqs expression
End

Theorem compute_case16594_direct_genuine_fast_eval_ok:
  compute_fast_eval_ok compute_case16594_direct_genuine_fast_eval
Proof
  mp_tac
    compute_boundedCase16594WordWholeDirectWitnessedFastDispatchTheory.bounded_case16594_word_whole_direct_witnessed_fast_eval_ok
  >> mp_tac compute_pureFastTheory.compute_pure_fast_eval_ok
  >> rw
       [computeTheory.compute_fast_eval_ok_def,
        compute_case16594_direct_genuine_fast_eval_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Definition compute_case16594_direct_genuine_fast_def:
  compute_case16594_direct_genuine_fast (ths,ceqs) tm =
    compute_with compute_case16594_direct_genuine_fast_eval (ths,ceqs) tm
End

Theorem compute_case16594_direct_genuine_fast_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_case16594_direct_genuine_fast (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_case16594_direct_genuine_fast_def]
  >> strip_tac
  >> assume_tac compute_case16594_direct_genuine_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `compute_case16594_direct_genuine_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
