(*****************************************************************************
 * First combined-environment gate for the genuine four-argument whole call. *
 *                                                                            *
 * The production dispatcher stays first in the equation list.  The imported *
 * whole-call equations are a lower-priority suffix, so the already proved   *
 * cell-0 dispatcher evaluation is preserved exactly.                         *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeCombinedEntry
Ancestors
  compute_boundedCase16594Cell0WholeHolLightCeqsAudit
  compute_boundedCase16594Cell0FastHolLightEntryClock
  compute_evalCeqsAppendSuccess
Libs
  bossLib preamble

Definition bounded_case16594_cell0_whole_combined_ceqs_def:
  bounded_case16594_cell0_whole_combined_ceqs =
    bounded_case16594_object_dispatch_cell0_ceqs ++
    bounded_case16594_cell0_whole_hol_light_ceqs
End

Theorem bounded_case16594_cell0_fast_hol_light_entry_eval_combined_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 3 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    bounded_case16594_cell0_fast_hol_light_entry (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> once_rewrite_tac [bounded_case16594_cell0_whole_combined_ceqs_def]
  >> irule
       (CONJUNCT1
         compute_evalCeqsAppendSuccessTheory.compute_eval_append_success)
  >> irule
       compute_boundedCase16594Cell0FastHolLightEntryClockTheory.bounded_case16594_cell0_fast_hol_light_entry_eval_clock
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
