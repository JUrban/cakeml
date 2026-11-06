(******************************************************************************
 * Frozen literal presentation of the authenticated case-16594 cell-0 entry. *
 *                                                                            *
 * The semantic entry is assembled from authenticated payload definitions.    *
 * This theory evaluates that closed assembly once, stores the resulting       *
 * compute_exp value, and proves byte-for-byte identity.  Translator and       *
 * executable probes can therefore exercise the production comparison without *
 * reimplementing any payload conversion.                                      *
 ******************************************************************************)
Theory compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteral
Ancestors
  compute_boundedCase16594Cell0AuthenticatedFastObjectEntry
  compute_registeredCase16594Cell0AuthenticatedFastObjectEntry
Libs
  bossLib preamble

val bounded_case16594_cell0_authenticated_fast_object_entry_literal_eval =
  EVAL
    ``bounded_case16594_cell0_authenticated_fast_object_entry_cexp``;

val bounded_case16594_cell0_authenticated_fast_object_entry_literal_tm =
  rhs
    (concl
      bounded_case16594_cell0_authenticated_fast_object_entry_literal_eval);

val bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp_def =
  new_definition
    ("bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp_def",
     mk_eq
       (mk_var
         ("bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp",
          ``:compute_exp``),
        bounded_case16594_cell0_authenticated_fast_object_entry_literal_tm));

Theorem bounded_case16594_cell0_authenticated_fast_object_entry_literal_identity:
  bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp =
  bounded_case16594_cell0_authenticated_fast_object_entry_cexp
Proof
  rw
    [bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp_def,
     bounded_case16594_cell0_authenticated_fast_object_entry_literal_eval]
QED

Definition registered_case16594_cell0_authenticated_fast_object_entry_literal_eval_def:
  registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
      ceqs cexp =
    if ceqs = bounded_case16594_object_dispatch_cell0_ceqs /\
       cexp =
         bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp
    then SOME (Num 1 : cv)
    else NONE
End

Theorem registered_case16594_cell0_authenticated_fast_object_entry_literal_eval_identity:
  registered_case16594_cell0_authenticated_fast_object_entry_literal_eval =
  registered_case16594_cell0_authenticated_fast_object_entry_eval
Proof
  simp
    [FUN_EQ_THM,
     registered_case16594_cell0_authenticated_fast_object_entry_literal_eval_def,
     compute_registeredCase16594Cell0AuthenticatedFastObjectEntryTheory.registered_case16594_cell0_authenticated_fast_object_entry_eval_def,
     bounded_case16594_cell0_authenticated_fast_object_entry_literal_identity]
QED

Theorem registered_case16594_cell0_authenticated_fast_object_entry_literal_eval_ok:
  compute_fast_eval_ok
    registered_case16594_cell0_authenticated_fast_object_entry_literal_eval
Proof
  rw
    [registered_case16594_cell0_authenticated_fast_object_entry_literal_eval_identity]
  >> irule
       compute_registeredCase16594Cell0AuthenticatedFastObjectEntryTheory.registered_case16594_cell0_authenticated_fast_object_entry_eval_ok
QED

val _ = export_theory ();
