(*****************************************************************************
 * Exact evaluator-core transfer into the case-16594 object dispatcher.
 *
 * The complete dispatcher extends the small packed-object acceptance
 * environment.  This theory authenticates that extension on the complete
 * closed call graph of the old environment, so its already-proved rational,
 * interval, quadratic, completion, and acceptance evaluator theorems can be
 * reused without evaluating or re-proving those functions.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectCoreCongruence
Ancestors
  compute_evalRestrictedCongruence
  compute_boundedPackedObjectEntryData
  compute_boundedCase16594ObjectDispatchCell0Data
Libs
  bossLib preamble

Definition bounded_case16594_object_core_def:
  bounded_case16594_object_core : mlstring list =
    MAP FST bounded_packed_object_entry_ceqs
End

Theorem bounded_case16594_object_core_count:
  LENGTH bounded_case16594_object_core = 27
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_core_old_closed:
  compute_ceqs_closed_on bounded_case16594_object_core
    bounded_packed_object_entry_ceqs
Proof
  irule compute_evalRestrictedCongruenceTheory.compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_core_agree:
  compute_ceqs_agree_on bounded_case16594_object_core
    bounded_packed_object_entry_ceqs
    bounded_case16594_object_dispatch_cell0_ceqs
Proof
  irule compute_evalRestrictedCongruenceTheory.compute_ceqs_agree_on_from_every
  >> EVAL_TAC
QED

Theorem compute_ceqs_closed_on_agree_right:
  compute_ceqs_closed_on allowed left_ceqs /\
  compute_ceqs_agree_on allowed left_ceqs right_ceqs ==>
  compute_ceqs_closed_on allowed right_ceqs
Proof
  rw
    [compute_evalRestrictedCongruenceTheory.compute_ceqs_closed_on_def,
     compute_evalRestrictedCongruenceTheory.compute_ceqs_agree_on_def]
  >> metis_tac []
QED

Theorem bounded_case16594_object_core_current_closed:
  compute_ceqs_closed_on bounded_case16594_object_core
    bounded_case16594_object_dispatch_cell0_ceqs
Proof
  irule compute_ceqs_closed_on_agree_right
  >> metis_tac
       [bounded_case16594_object_core_old_closed,
        bounded_case16594_object_core_agree]
QED

Theorem bounded_case16594_object_core_eval_cong:
  compute_exp_uses_only bounded_case16594_object_core expression ==>
  compute_eval clock bounded_packed_object_entry_ceqs expression
      (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs expression
      refs
Proof
  strip_tac
  >> irule
       (CONJUNCT1
         compute_evalRestrictedCongruenceTheory.compute_eval_restricted_cong)
  >> metis_tac
       [bounded_case16594_object_core_old_closed,
        bounded_case16594_object_core_current_closed,
        bounded_case16594_object_core_agree]
QED

Theorem bounded_case16594_object_core_uses_only_from_cv:
  compute_exp_uses_only allowed (from_cv value)
Proof
  metis_tac
    [compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv]
QED

Theorem bounded_case16594_object_core_literal_app_eval_cong:
  MEM (function_name:mlstring) bounded_case16594_object_core ==>
  compute_eval clock bounded_packed_object_entry_ceqs
      (App function_name (MAP from_cv payloads)) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App function_name (MAP from_cv payloads)) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_core_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        EVERY_MAP,
        bounded_case16594_object_core_uses_only_from_cv]
QED

Theorem bounded_case16594_object_core_literal_app_eval_from_old:
  MEM (function_name:mlstring) bounded_case16594_object_core /\
  compute_eval clock bounded_packed_object_entry_ceqs
      (App function_name (MAP from_cv payloads)) (refs:hol_refs) = outcome ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App function_name (MAP from_cv payloads)) refs = outcome
Proof
  strip_tac
  >> `compute_eval clock bounded_packed_object_entry_ceqs
        (App function_name (MAP from_cv payloads)) (refs:hol_refs) =
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App function_name (MAP from_cv payloads)) refs` by
       (irule bounded_case16594_object_core_literal_app_eval_cong
        >> asm_rewrite_tac [])
  >> metis_tac []
QED

val _ = export_theory ();
