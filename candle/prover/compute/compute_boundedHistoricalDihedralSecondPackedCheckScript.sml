(*****************************************************************************
 * Streaming development checker for the genuine historical-dihedral box
 * value, gradient, and upper-triangular Hessian.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralSecondPackedCheck
Ancestors
  compute_boundedHistoricalDihedralSecond
  compute_boundedHistoricalDihedralFirstPackedCheck
Libs
  bossLib preamble

Definition bounded_packed_chars_historical_second_cell_def:
  bounded_packed_chars_historical_second_cell bytes =
    bounded_packed_chars_interval64_list 45 bytes
End

Definition bounded_packed_historical_second_cell_ok_def:
  bounded_packed_historical_second_cell_ok values ⇔
    case values of
    | e0::e1::e2::e3::e4::e5::root_delta::root_four_x0::
        r0::r1::r2::r3::r4::r5::r6::r7::r8::expected_value::
        g0::g1::g2::g3::g4::g5::
        h00::h01::h02::h03::h04::h05::
        h11::h12::h13::h14::h15::
        h22::h23::h24::h25::
        h33::h34::h35::h44::h45::h55::[] =>
      bounded_historical_dihedral_second64
        [e0;e1;e2;e3;e4;e5] root_delta root_four_x0
        [r0;r1;r2;r3;r4;r5;r6;r7;r8] =
        SOME
          (expected_value,[g0;g1;g2;g3;g4;g5],
           [h00;h01;h02;h03;h04;h05;
            h11;h12;h13;h14;h15;
            h22;h23;h24;h25;
            h33;h34;h35;h44;h45;h55])
    | _ => F
End

Definition bounded_packed_chars_historical_second_cells_def:
  bounded_packed_chars_historical_second_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_historical_second_cells (SUC remaining) bytes count =
    case bounded_packed_chars_historical_second_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
      if bounded_packed_historical_second_cell_ok cell then
        bounded_packed_chars_historical_second_cells
          remaining rest (SUC count)
      else NONE
End

Definition bounded_packed_chars_historical_second_header_def:
  bounded_packed_chars_historical_second_header bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"H";#"D";#"S";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,finish) =>
        if cells = 1w then SOME ((1:num),finish)
        else if cells = 4173w then SOME ((4173:num),finish)
        else NONE
End

Definition bounded_packed_chars_historical_second_complete_check_def:
  bounded_packed_chars_historical_second_complete_check bytes ⇔
    case bounded_packed_chars_historical_second_header bytes of
    | NONE => F
    | SOME (cells,rest) =>
        bounded_packed_chars_historical_second_cells cells rest 0 = SOME cells
End

val _ = export_theory ();
