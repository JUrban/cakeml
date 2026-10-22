(* CakeML translation of the complete historical-dihedral box/Hessian gate. *)
Theory compute_boundedHistoricalDihedralSecondPackedCheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedHistoricalDihedralFirstPackedCheckProg
  compute_boundedHistoricalDihedralSecondPackedCheck

val _ = translation_extends
  "compute_boundedHistoricalDihedralFirstPackedCheckProg";

val bounded_historical_extreme_interval_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_extreme_interval_def;
val bounded_historical_monotone_coordinate_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def;
val bounded_historical_monotone_environment_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_environment_def;
val bounded_historical_delta_gradient_component_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_gradient_component_def;
val bounded_historical_delta_gradient_box_entry_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_gradient_box_entry_def;
val bounded_historical_delta_gradient_box_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_gradient_box_def;
val bounded_historical_delta_second_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_second_def;
val bounded_historical_delta_x4_value_block_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_x4_value_block_def;
val bounded_historical_delta_x4_hessian_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_x4_hessian_def;
val bounded_historical_delta_x4_second_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_x4_second_def;
val bounded_historical_sqrt_hessian_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_sqrt_hessian_def;
val bounded_historical_sqrt_second_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_sqrt_second_def;
val bounded_historical_b_hessian_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_b_hessian_def;
val bounded_historical_second_hessian_entry_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_second_hessian_entry_def;
val bounded_historical_second_hessian_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_second_hessian_def;
val bounded_historical_dihedral_second64_v =
  translate
    compute_boundedHistoricalDihedralSecondTheory.bounded_historical_dihedral_second64_def;

val bounded_packed_chars_historical_second_cell_v =
  translate
    compute_boundedHistoricalDihedralSecondPackedCheckTheory.bounded_packed_chars_historical_second_cell_def;
val bounded_packed_historical_second_cell_ok_v =
  translate
    compute_boundedHistoricalDihedralSecondPackedCheckTheory.bounded_packed_historical_second_cell_ok_def;
val bounded_packed_chars_historical_second_cells_v =
  translate
    compute_boundedHistoricalDihedralSecondPackedCheckTheory.bounded_packed_chars_historical_second_cells_def;
val bounded_packed_chars_historical_second_header_v =
  translate
    compute_boundedHistoricalDihedralSecondPackedCheckTheory.bounded_packed_chars_historical_second_header_def;
val bounded_packed_chars_historical_second_complete_check_v =
  translate
    compute_boundedHistoricalDihedralSecondPackedCheckTheory.bounded_packed_chars_historical_second_complete_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_historical_second_complete_check
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

Definition compute_bounded_historical_dihedral_second_check_prog_def:
  compute_bounded_historical_dihedral_second_check_prog = ^prog
End

val _ = export_theory ();
