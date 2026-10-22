(*****************************************************************************
 * Development-only parse control for the historical-dihedral first-order
 * payload.  It decodes exactly the same twenty intervals per cell but does
 * not execute or compare the numerical checker.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralFirstParseControl
Ancestors
  compute_boundedHistoricalDihedralFirstPackedCheck
Libs
  bossLib preamble

Definition bounded_packed_chars_historical_first_parse_cells_def:
  bounded_packed_chars_historical_first_parse_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_historical_first_parse_cells (SUC remaining)
      bytes count =
    case bounded_packed_chars_historical_first_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        bounded_packed_chars_historical_first_parse_cells remaining rest
          (SUC count)
End

Definition bounded_packed_chars_historical_first_parse_control_def:
  bounded_packed_chars_historical_first_parse_control bytes ⇔
    case bounded_packed_chars_historical_first_header bytes of
    | NONE => F
    | SOME (cells,rest) =>
        bounded_packed_chars_historical_first_parse_cells cells rest 0 =
          SOME cells
End

Theorem bounded_packed_chars_historical_first_parse_control_truncated:
  ¬bounded_packed_chars_historical_first_parse_control []
Proof
  EVAL_TAC
QED

val _ = export_theory ();
