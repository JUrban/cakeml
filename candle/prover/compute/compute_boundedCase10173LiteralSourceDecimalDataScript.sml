(*****************************************************************************
 * Closed development fixture for the source-shaped bounded checker.
 *****************************************************************************)
Theory compute_boundedCase10173LiteralSourceDecimalData
Ancestors
  compute_boundedCase10173LiteralSourceDecimal
  compute_boundedCase10173HistoricalCellDecimalData
Libs
  bossLib preamble wordsLib

Theorem bounded_case10173_decimal_packet0_literal_source_accepts:
  bounded_case10173_literal_source_accepts_decimal
    bounded_case10173_decimal_packet0
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
