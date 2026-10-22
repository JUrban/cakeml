(*****************************************************************************
 * Composition of proved fast evaluators.
 *
 * A successful earlier evaluator is authoritative under its own refinement
 * theorem.  NONE delegates to the next evaluator; after the complete chain
 * misses, compute_with retains its existing verified generic fallback.
 *****************************************************************************)
Theory compute_fastChain
Ancestors
  computeProof compute_pureFast compute_registeredCase10173Cell0Fast
Libs
  bossLib preamble

Definition compute_fast_eval_chain_def:
  compute_fast_eval_chain evaluator1 evaluator2 ceqs cexp =
    case evaluator1 ceqs cexp of
    | SOME result => SOME result
    | NONE => evaluator2 ceqs cexp
End

Theorem compute_fast_eval_chain_ok:
  compute_fast_eval_ok evaluator1 /\
  compute_fast_eval_ok evaluator2 ==>
  compute_fast_eval_ok (compute_fast_eval_chain evaluator1 evaluator2)
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      compute_fast_eval_chain_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Definition compute_case10173_cell0_fast_eval_def:
  compute_case10173_cell0_fast_eval =
    compute_fast_eval_chain
      registered_case10173_cell0_fast_eval
      compute_pure_fast_eval
End

Theorem compute_case10173_cell0_fast_eval_ok:
  compute_fast_eval_ok compute_case10173_cell0_fast_eval
Proof
  rw [compute_case10173_cell0_fast_eval_def]
  >> irule compute_fast_eval_chain_ok
  >> simp [compute_registeredCase10173Cell0FastTheory.registered_case10173_cell0_fast_eval_ok,
           compute_pureFastTheory.compute_pure_fast_eval_ok]
QED

Definition compute_case10173_cell0_fast_def:
  compute_case10173_cell0_fast (ths,ceqs) tm =
    compute_with compute_case10173_cell0_fast_eval (ths,ceqs) tm
End

Theorem compute_case10173_cell0_fast_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_case10173_cell0_fast (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_case10173_cell0_fast_def]
  >> strip_tac
  >> assume_tac compute_case10173_cell0_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `compute_case10173_cell0_fast_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
