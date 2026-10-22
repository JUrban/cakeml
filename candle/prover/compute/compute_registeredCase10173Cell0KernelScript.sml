(*****************************************************************************
 * Kernel-facing prototype for the first genuine registered fast NL result.
 *
 * This deliberately caches only the already-proved exact cell-0 result.  It
 * tests the theorem-producing kernel handoff without translating or executing
 * the generic evaluator.  The scalable production evaluator will replace
 * this exact registration with the proved word-checker decoder/refinement.
 *****************************************************************************)
Theory compute_registeredCase10173Cell0Kernel
Ancestors
  computeProof
  compute_registeredCase10173Cell0Fast
Libs
  bossLib preamble

Definition registered_case10173_cell0_cached_eval_def:
  registered_case10173_cell0_cached_eval ceqs cexp =
    if ceqs = registered_case10173_cell0_ceqs /\
       cexp = registered_case10173_cell0_cexp
    then SOME registered_case10173_cell0_result
    else NONE
End

Theorem registered_case10173_cell0_cached_eval_ok:
  compute_fast_eval_ok registered_case10173_cell0_cached_eval
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      registered_case10173_cell0_cached_eval_def]
  >> every_case_tac
  >> gvs [registered_case10173_cell0_compute_eval]
QED

Definition compute_registered_case10173_cell0_def:
  compute_registered_case10173_cell0 (ths,ceqs) tm =
    compute_with registered_case10173_cell0_cached_eval (ths,ceqs) tm
End

Theorem compute_registered_case10173_cell0_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_registered_case10173_cell0 (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_registered_case10173_cell0_def]
  >> strip_tac
  >> assume_tac registered_case10173_cell0_cached_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac `registered_case10173_cell0_cached_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
