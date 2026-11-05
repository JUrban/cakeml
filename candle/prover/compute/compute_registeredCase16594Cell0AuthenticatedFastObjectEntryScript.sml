(******************************************************************************
 * Trusted fast-evaluator registration for the authenticated genuine          *
 * case-16594 cell-0 object entry.                                             *
 *                                                                            *
 * The callback recognizes both the exact dispatcher environment and the      *
 * exact fast-certificate entry expression.  Its result is justified by the   *
 * complete checked entry evaluator theorem; the callback itself is not an     *
 * additional trusted computation.                                            *
 ******************************************************************************)
Theory compute_registeredCase16594Cell0AuthenticatedFastObjectEntry
Ancestors
  computeProof
  compute_boundedCase16594Cell0AuthenticatedFastObjectEntry
Libs
  bossLib preamble

Definition registered_case16594_cell0_authenticated_fast_object_entry_eval_def:
  registered_case16594_cell0_authenticated_fast_object_entry_eval ceqs cexp =
    if ceqs = bounded_case16594_object_dispatch_cell0_ceqs /\
       cexp = bounded_case16594_cell0_authenticated_fast_object_entry_cexp
    then SOME (Num 1 : cv)
    else NONE
End

Theorem registered_case16594_cell0_authenticated_fast_object_entry_compute_eval:
  !s.
    compute_eval compute_default_clock
      bounded_case16594_object_dispatch_cell0_ceqs
      bounded_case16594_cell0_authenticated_fast_object_entry_cexp s =
    (M_success (from_cv (Num 1 : cv)),s)
Proof
  simp
    [compute_boundedCase16594Cell0AuthenticatedFastObjectEntryTheory.bounded_case16594_cell0_authenticated_fast_object_entry_eval]
QED

Theorem registered_case16594_cell0_authenticated_fast_object_entry_eval_hit:
  registered_case16594_cell0_authenticated_fast_object_entry_eval
    bounded_case16594_object_dispatch_cell0_ceqs
    bounded_case16594_cell0_authenticated_fast_object_entry_cexp =
  SOME (Num 1 : cv)
Proof
  simp
    [registered_case16594_cell0_authenticated_fast_object_entry_eval_def]
QED

Theorem registered_case16594_cell0_authenticated_fast_object_entry_eval_ok:
  compute_fast_eval_ok
    registered_case16594_cell0_authenticated_fast_object_entry_eval
Proof
  rw
    [computeTheory.compute_fast_eval_ok_def,
     registered_case16594_cell0_authenticated_fast_object_entry_eval_def]
  >> every_case_tac
  >> gvs
       [registered_case16594_cell0_authenticated_fast_object_entry_compute_eval]
QED

Definition compute_registered_case16594_cell0_authenticated_fast_object_entry_def:
  compute_registered_case16594_cell0_authenticated_fast_object_entry
      (ths,ceqs) tm =
    compute_with
      registered_case16594_cell0_authenticated_fast_object_entry_eval
      (ths,ceqs) tm
End

Theorem compute_registered_case16594_cell0_authenticated_fast_object_entry_thm:
  STATE ctxt s /\
  EVERY (THM ctxt) ths /\
  EVERY (THM ctxt) ceqs /\
  TERM ctxt tm ==>
  compute_registered_case16594_cell0_authenticated_fast_object_entry
    (ths,ceqs) tm s = (res,s') ==>
    s' = s /\
    (!th. res = M_success th ==> THM ctxt th) /\
    (!tm. res <> M_failure (Clash tm))
Proof
  strip_tac
  >> fs
       [compute_registered_case16594_cell0_authenticated_fast_object_entry_def]
  >> strip_tac
  >> assume_tac
       registered_case16594_cell0_authenticated_fast_object_entry_eval_ok
  >> irule computeProofTheory.compute_with_thm
  >> simp []
  >> qexists_tac `ceqs`
  >> qexists_tac
       `registered_case16594_cell0_authenticated_fast_object_entry_eval`
  >> qexists_tac `ths`
  >> qexists_tac `tm`
  >> simp []
QED

val _ = export_theory ();
