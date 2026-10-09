(*****************************************************************************
 * Development-only packed checker for the first 128 genuine case10173
 * historical delta blocks.  The external fixture carries six scale-2^40
 * input intervals and the exact native-oracle result for each cell.  This is
 * a transfer/performance gate, not the final analytic checker interface.
 *****************************************************************************)
Theory compute_boundedHistoricalDeltaPackedCheck
Ancestors
  compute_boundedHistoricalDelta compute_boundedPackedSequentialInput
Libs
  bossLib preamble

Definition bounded_packed_chars_historical_delta_cell_def:
  bounded_packed_chars_historical_delta_cell bytes =
    case bounded_packed_chars_positive_interval64_list 6 bytes of
    | NONE => NONE
    | SOME (environment,rest) =>
      case bounded_packed_chars_interval64 rest of
      | NONE => NONE
      | SOME (expected,finish) =>
          SOME ((environment,expected),finish)
End

Definition bounded_packed_chars_historical_delta_header_def:
  bounded_packed_chars_historical_delta_header bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"H";#"D";#"B";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,finish) =>
          if cells = 128w then SOME finish else NONE
End

Definition bounded_packed_chars_historical_delta_cell_ok_def:
  bounded_packed_chars_historical_delta_cell_ok (environment,expected) ⇔
    bounded_historical_delta64_value environment = SOME expected
End

Definition bounded_packed_chars_historical_delta_cells_def:
  bounded_packed_chars_historical_delta_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_historical_delta_cells (SUC remaining) bytes count =
    case bounded_packed_chars_historical_delta_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        if bounded_packed_chars_historical_delta_cell_ok cell then
          bounded_packed_chars_historical_delta_cells remaining rest
            (SUC count)
        else NONE
End

Definition bounded_packed_chars_historical_delta_complete_check_def:
  bounded_packed_chars_historical_delta_complete_check bytes ⇔
    case bounded_packed_chars_historical_delta_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_historical_delta_cells 128 rest 0 = SOME 128
End

Definition bounded_packed_historical_delta_complete_check_def:
  bounded_packed_historical_delta_complete_check (strlit bytes) ⇔
    bounded_packed_chars_historical_delta_complete_check bytes
End

Theorem bounded_packed_chars_historical_delta_complete_check_truncated:
  ¬bounded_packed_chars_historical_delta_complete_check []
Proof
  EVAL_TAC
QED

Theorem bounded_packed_historical_delta_complete_check_truncated:
  ¬bounded_packed_historical_delta_complete_check «»
Proof
  EVAL_TAC
QED

val _ = export_theory ();
