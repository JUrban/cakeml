(* CakeML translation of the complete historical-dihedral center-jet gate. *)
Theory compute_boundedHistoricalDihedralFirstPackedCheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedHistoricalDeltaFullCheckProg
  compute_boundedHistoricalDihedralFirstPackedCheck

val _ = translation_extends "compute_boundedHistoricalDeltaFullCheckProg";

val bounded_historical_scale2_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def;
val bounded_historical_point_lower_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def;
val bounded_historical_point_upper_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def;
val bounded_historical_u_upper_negative_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_negative_def;
val bounded_historical_u_upper_positive_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_positive_def;
val bounded_historical_u_lower_negative_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_negative_def;
val bounded_historical_u_lower_positive_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_positive_def;
val bounded_historical_u_block_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_block_def;
val bounded_historical_u_three_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_three_def;
val bounded_historical_u126_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u126_def;
val bounded_historical_u135_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u135_def;
val bounded_historical_delta_x4_value_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_value_def;
val bounded_historical_delta_x4_gradient_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def;
val bounded_historical_c_vector_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_c_vector_def;
val bounded_historical_replace_three_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_replace_three_def;
val bounded_historical_dihedral_first64_v =
  translate
    compute_boundedHistoricalDihedralFirstTheory.bounded_historical_dihedral_first64_def;

val bounded_packed_chars_interval64_list_v =
  translate
    compute_boundedHistoricalDihedralFirstPackedCheckTheory.bounded_packed_chars_interval64_list_def;
val bounded_packed_chars_historical_first_cell_v =
  translate
    compute_boundedHistoricalDihedralFirstPackedCheckTheory.bounded_packed_chars_historical_first_cell_def;
val bounded_packed_historical_first_cell_ok_v =
  translate
    compute_boundedHistoricalDihedralFirstPackedCheckTheory.bounded_packed_historical_first_cell_ok_def;
val bounded_packed_chars_historical_first_cells_v =
  translate
    compute_boundedHistoricalDihedralFirstPackedCheckTheory.bounded_packed_chars_historical_first_cells_def;
val bounded_packed_chars_historical_first_header_v =
  translate
    compute_boundedHistoricalDihedralFirstPackedCheckTheory.bounded_packed_chars_historical_first_header_def;
val bounded_packed_chars_historical_first_complete_check_v =
  translate
    compute_boundedHistoricalDihedralFirstPackedCheckTheory.bounded_packed_chars_historical_first_complete_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_historical_first_complete_check
         (String.explode payload)
    then TextIO.print "accepted\n"
    else TextIO.print "rejected\n"
  end;
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_bounded_historical_dihedral_first_check_prog_def:
  compute_bounded_historical_dihedral_first_check_prog = ^prog
End

val _ = export_theory ();
