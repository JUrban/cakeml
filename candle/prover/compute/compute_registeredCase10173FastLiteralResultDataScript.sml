(*****************************************************************************
 * Stable materialization boundary for the corrected fast literal result.
 *
 * Keep the four-minute closed calculation separate from the changing
 * evaluator handoff so later namespace or theorem-shape edits do not replay
 * it.
 *****************************************************************************)
Theory compute_registeredCase10173FastLiteralResultData
Ancestors
  compute_registeredCase10173SourceAlignedLiteralData
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_fast_literal_result_def:
  registered_case10173_fast_literal_result =
    case bounded_case10173_literal_source_decimal
      bounded_case10173_decimal_packet0_source_aligned of
    | NONE => ARB
    | SOME result => result
End

Theorem registered_case10173_fast_literal_result_exact:
  bounded_case10173_literal_source_decimal
      bounded_case10173_decimal_packet0_source_aligned =
    SOME registered_case10173_fast_literal_result
Proof
  mp_tac
    compute_registeredCase10173SourceAlignedLiteralDataTheory.registered_case10173_source_aligned_literal_source_accepts
  >> strip_tac
  >> drule
       compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_source_accepts_contract
  >> strip_tac
  >> simp [registered_case10173_fast_literal_result_def]
QED

val registered_case10173_fast_literal_result_value =
  time EVAL ``registered_case10173_fast_literal_result``;
val _ = save_thm
  ("registered_case10173_fast_literal_result_value",
   registered_case10173_fast_literal_result_value);
val _ = cv_trans registered_case10173_fast_literal_result_value;

val _ = export_theory ();
