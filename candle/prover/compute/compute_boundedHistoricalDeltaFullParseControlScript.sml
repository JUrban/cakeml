(*****************************************************************************
 * Development-only parse control for the complete historical-delta payload.
 *
 * This deliberately does not check the expected numerical results.  It is a
 * held-input timing control for attributing packed decoding and traversal;
 * it must never be used as certificate or release evidence.
 *****************************************************************************)
Theory compute_boundedHistoricalDeltaFullParseControl
Ancestors
  compute_boundedHistoricalDeltaFullCheck
Libs
  bossLib preamble

Definition bounded_packed_chars_historical_delta_parse_cells_def:
  bounded_packed_chars_historical_delta_parse_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_historical_delta_parse_cells (SUC remaining)
      bytes count =
    case bounded_packed_chars_historical_delta_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        bounded_packed_chars_historical_delta_parse_cells remaining rest
          (SUC count)
End

Definition bounded_packed_chars_historical_delta_full_parse_control_def:
  bounded_packed_chars_historical_delta_full_parse_control bytes ⇔
    case bounded_packed_chars_historical_delta_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_historical_delta_parse_cells 4173 rest 0 =
          SOME 4173
End

Theorem bounded_packed_chars_historical_delta_full_parse_control_truncated:
  ¬bounded_packed_chars_historical_delta_full_parse_control []
Proof
  EVAL_TAC
QED

val _ = export_theory ();
