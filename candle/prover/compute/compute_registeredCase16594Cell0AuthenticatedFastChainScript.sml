(******************************************************************************
 * Production evaluator chain with the authenticated genuine case-16594      *
 * cell-0 object entry ahead of the existing Candle fast-evaluator chain.     *
 *                                                                            *
 * Only the exact equation environment and exact fast-certificate entry hit.  *
 * Every other call delegates unchanged to the already installed evaluator.   *
 ******************************************************************************)
Theory compute_registeredCase16594Cell0AuthenticatedFastChain
Ancestors
  compute_fastPrepend
  compute_registeredCase16594Cell0AuthenticatedFastObjectEntry
Libs
  bossLib preamble

Definition compute_case16594_cell0_authenticated_fast_eval_def:
  compute_case16594_cell0_authenticated_fast_eval fallback ceqs cexp =
    compute_fast_eval_prepend
      registered_case16594_cell0_authenticated_fast_object_entry_eval
      fallback ceqs cexp
End

Theorem compute_case16594_cell0_authenticated_fast_eval_ok:
  compute_fast_eval_ok fallback ==>
  compute_fast_eval_ok
    (compute_case16594_cell0_authenticated_fast_eval fallback)
Proof
  strip_tac
  >> `compute_case16594_cell0_authenticated_fast_eval fallback =
        compute_fast_eval_prepend
          registered_case16594_cell0_authenticated_fast_object_entry_eval
          fallback` by
       simp
         [FUN_EQ_THM,
          compute_case16594_cell0_authenticated_fast_eval_def]
  >> asm_rewrite_tac []
  >> irule compute_fastPrependTheory.compute_fast_eval_prepend_ok
  >> simp
       [compute_registeredCase16594Cell0AuthenticatedFastObjectEntryTheory.registered_case16594_cell0_authenticated_fast_object_entry_eval_ok]
QED

Theorem compute_case16594_cell0_authenticated_fast_eval_hit:
  compute_case16594_cell0_authenticated_fast_eval fallback
    bounded_case16594_object_dispatch_cell0_ceqs
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp =
  SOME (Num 1 : cv)
Proof
  simp
    [compute_case16594_cell0_authenticated_fast_eval_def,
     compute_fastPrependTheory.compute_fast_eval_prepend_def,
     compute_registeredCase16594Cell0AuthenticatedFastObjectEntryTheory.registered_case16594_cell0_authenticated_fast_object_entry_eval_hit]
QED

Theorem compute_case16594_cell0_authenticated_fast_eval_ceqs_miss:
  altered_ceqs <> bounded_case16594_object_dispatch_cell0_ceqs ==>
  registered_case16594_cell0_authenticated_fast_object_entry_eval
    altered_ceqs bounded_case16594_cell0_authenticated_fast_object_entry_cexp =
  NONE
Proof
  simp
    [compute_registeredCase16594Cell0AuthenticatedFastObjectEntryTheory.registered_case16594_cell0_authenticated_fast_object_entry_eval_def]
QED

Theorem compute_case16594_cell0_authenticated_fast_eval_entry_miss:
  altered_entry <>
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp ==>
  registered_case16594_cell0_authenticated_fast_object_entry_eval
    bounded_case16594_object_dispatch_cell0_ceqs altered_entry = NONE
Proof
  simp
    [compute_registeredCase16594Cell0AuthenticatedFastObjectEntryTheory.registered_case16594_cell0_authenticated_fast_object_entry_eval_def]
QED

Theorem compute_case16594_cell0_authenticated_fast_eval_ceqs_fallback:
  altered_ceqs <> bounded_case16594_object_dispatch_cell0_ceqs ==>
  compute_case16594_cell0_authenticated_fast_eval fallback altered_ceqs
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp =
  fallback altered_ceqs
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp
Proof
  simp
    [compute_case16594_cell0_authenticated_fast_eval_def,
     compute_fastPrependTheory.compute_fast_eval_prepend_def,
     compute_case16594_cell0_authenticated_fast_eval_ceqs_miss]
QED

Theorem compute_case16594_cell0_authenticated_fast_eval_entry_fallback:
  altered_entry <>
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp ==>
  compute_case16594_cell0_authenticated_fast_eval fallback
    bounded_case16594_object_dispatch_cell0_ceqs altered_entry =
  fallback bounded_case16594_object_dispatch_cell0_ceqs altered_entry
Proof
  simp
    [compute_case16594_cell0_authenticated_fast_eval_def,
     compute_fastPrependTheory.compute_fast_eval_prepend_def,
     compute_case16594_cell0_authenticated_fast_eval_entry_miss]
QED

Definition compute_case16594_cell0_authenticated_fast_def:
  compute_case16594_cell0_authenticated_fast fallback (ths,ceqs) tm =
    compute_with (compute_case16594_cell0_authenticated_fast_eval fallback)
      (ths,ceqs) tm
End

Theorem compute_case16594_cell0_authenticated_fast_thm:
  compute_fast_eval_ok fallback /\
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_case16594_cell0_authenticated_fast fallback (ths,ceqs) tm s =
    (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs [compute_case16594_cell0_authenticated_fast_def]
  >> strip_tac
  >> imp_res_tac compute_case16594_cell0_authenticated_fast_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `compute_case16594_cell0_authenticated_fast_eval fallback`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
