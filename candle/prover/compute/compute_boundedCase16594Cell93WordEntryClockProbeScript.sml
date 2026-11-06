(*****************************************************************************
 * Bounded probe: retain the clock-parametric production-entry theorem for   *
 * one already authenticated genuine case-16594 cell.                        *
 *                                                                            *
 * The all-cell whole-call recursion invokes each entry below the initial     *
 * default clock.  This probe checks that the closed cell premises discharge  *
 * the existing generic theorem without replaying numerical authentication.   *
 *****************************************************************************)
Theory compute_boundedCase16594Cell93WordEntryClockProbe
Ancestors
  compute_boundedCase16594Cells0093To0108WordAuth
Libs
  bossLib preamble

Theorem bounded_case16594_all_cell0093_word_converted_entry_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 3 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    bounded_case16594_all_cell0093_word_converted_entry_cexp
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_all_cell0093_word_converted_entry_cexp_def]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
          compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_complete_accepted_entry_eval)
  >> asm_rewrite_tac
       [bounded_case16594_all_cell0093_word_radii_length,
        bounded_case16594_all_cell0093_word_center_boxes_length,
        bounded_case16594_all_cell0093_word_outer_boxes_length,
        bounded_case16594_all_cell0093_word_center_boxes_valid,
        bounded_case16594_all_cell0093_word_outer_boxes_valid,
        bounded_case16594_all_cell0093_word_radius_pairs,
        bounded_case16594_all_cell0093_word_runtime_trace_call_exact,
        bounded_case16594_all_cell0093_word_dispatch_packet_contracts,
        bounded_case16594_all_cell0093_word_result_accepts]
  >> metis_tac
       [bounded_case16594_all_cell0093_word_runtime_trace_call_exact,
        bounded_case16594_all_cell0093_word_dispatch_packet_contracts,
        bounded_case16594_all_cell0093_word_result_accepts]
QED

val _ = export_theory ();
