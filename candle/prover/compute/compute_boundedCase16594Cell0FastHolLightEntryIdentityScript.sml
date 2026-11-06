(*****************************************************************************
 * Cross-system identity for the audited HOL Light case-16594 cell-0 entry.  *
 *                                                                            *
 * The imported definition is untrusted generated data.  This theorem admits *
 * it only after constructor-level equality with the already-authenticated    *
 * fast entry.                                                                *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0FastHolLightEntryIdentity
Ancestors
  compute_boundedCase16594Cell0FastHolLightEntryData
  compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteral
Libs
  bossLib preamble

Theorem bounded_case16594_cell0_fast_hol_light_entry_literal_identity:
  bounded_case16594_cell0_fast_hol_light_entry =
  bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp
Proof
  simp
    [compute_boundedCase16594Cell0FastHolLightEntryDataTheory.bounded_case16594_cell0_fast_hol_light_entry_def,
     compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteralTheory.bounded_case16594_cell0_authenticated_fast_object_entry_literal_cexp_def]
QED

Theorem bounded_case16594_cell0_fast_hol_light_entry_authenticated_identity:
  bounded_case16594_cell0_fast_hol_light_entry =
  bounded_case16594_cell0_authenticated_fast_object_entry_cexp
Proof
  metis_tac
    [bounded_case16594_cell0_fast_hol_light_entry_literal_identity,
     compute_boundedCase16594Cell0AuthenticatedFastObjectEntryLiteralTheory.bounded_case16594_cell0_authenticated_fast_object_entry_literal_identity]
QED

val _ = export_theory ();
