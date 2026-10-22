(*****************************************************************************
 * Streaming development checker for the genuine historical-dihedral center
 * jet.  The full payload has 4,173 cells; a one-cell payload is accepted only
 * to keep the edit/test loop small before the complete run.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralFirstPackedCheck
Ancestors
  compute_boundedHistoricalDihedralFirst compute_boundedPackedSequentialInput
Libs
  bossLib preamble

Definition bounded_packed_chars_interval64_list_def:
  bounded_packed_chars_interval64_list 0 bytes = SOME ([],bytes) ∧
  bounded_packed_chars_interval64_list (SUC remaining) bytes =
    case bounded_packed_chars_interval64 bytes of
    | NONE => NONE
    | SOME (value,rest) =>
      case bounded_packed_chars_interval64_list remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (value::suffix,finish)
End

Definition bounded_packed_chars_historical_first_cell_def:
  bounded_packed_chars_historical_first_cell bytes =
    bounded_packed_chars_interval64_list 20 bytes
End

Definition bounded_packed_historical_first_cell_ok_def:
  bounded_packed_historical_first_cell_ok values ⇔
    case values of
    | e0::e1::e2::e3::e4::e5::root_delta::root_four_x0::
        r0::r1::r2::r3::r4::expected_value::
        g0::g1::g2::g3::g4::g5::[] =>
      bounded_historical_dihedral_first64
        [e0;e1;e2;e3;e4;e5] root_delta root_four_x0 [r0;r1;r2;r3;r4] =
        SOME (expected_value,[g0;g1;g2;g3;g4;g5])
    | _ => F
End

Definition bounded_packed_chars_historical_first_cells_def:
  bounded_packed_chars_historical_first_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_historical_first_cells (SUC remaining) bytes count =
    case bounded_packed_chars_historical_first_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
      if bounded_packed_historical_first_cell_ok cell then
        bounded_packed_chars_historical_first_cells remaining rest (SUC count)
      else NONE
End

Definition bounded_packed_chars_historical_first_header_def:
  bounded_packed_chars_historical_first_header bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"H";#"D";#"F";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,finish) =>
        if cells = 1w then SOME ((1:num),finish)
        else if cells = 4173w then SOME ((4173:num),finish)
        else NONE
End

Definition bounded_packed_chars_historical_first_complete_check_def:
  bounded_packed_chars_historical_first_complete_check bytes ⇔
    case bounded_packed_chars_historical_first_header bytes of
    | NONE => F
    | SOME (cells,rest) =>
        bounded_packed_chars_historical_first_cells cells rest 0 = SOME cells
End

Definition bounded_packed_historical_first_complete_check_def:
  bounded_packed_historical_first_complete_check (strlit bytes) ⇔
    bounded_packed_chars_historical_first_complete_check bytes
End

val _ = export_theory ();
