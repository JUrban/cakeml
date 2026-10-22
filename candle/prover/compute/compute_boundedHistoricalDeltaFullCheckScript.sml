(*****************************************************************************
 * Development-only packed checker for all 4,173 genuine case10173
 * historical delta blocks.  The cell parser and checked historical operation
 * are inherited unchanged from the prefix-128 transfer gate.
 *****************************************************************************)
Theory compute_boundedHistoricalDeltaFullCheck
Ancestors
  compute_boundedHistoricalDeltaPackedCheck
Libs
  bossLib preamble

Definition bounded_packed_chars_historical_delta_full_header_def:
  bounded_packed_chars_historical_delta_full_header bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"H";#"D";#"B";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,finish) =>
          if cells = 4173w then SOME finish else NONE
End

Definition bounded_packed_chars_historical_delta_full_check_def:
  bounded_packed_chars_historical_delta_full_check bytes ⇔
    case bounded_packed_chars_historical_delta_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_historical_delta_cells 4173 rest 0 = SOME 4173
End

Definition bounded_packed_historical_delta_full_check_def:
  bounded_packed_historical_delta_full_check (strlit bytes) ⇔
    bounded_packed_chars_historical_delta_full_check bytes
End

Theorem bounded_packed_chars_historical_delta_full_check_truncated:
  ¬bounded_packed_chars_historical_delta_full_check []
Proof
  EVAL_TAC
QED

Theorem bounded_packed_historical_delta_full_check_truncated:
  ¬bounded_packed_historical_delta_full_check «»
Proof
  EVAL_TAC
QED

val _ = export_theory ();
