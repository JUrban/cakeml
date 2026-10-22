(* CakeML translation of the first-order payload parse-only timing control. *)
Theory compute_boundedHistoricalDihedralFirstParseControlProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedHistoricalDihedralFirstPackedCheckProg
  compute_boundedHistoricalDihedralFirstParseControl

val _ = translation_extends
  "compute_boundedHistoricalDihedralFirstPackedCheckProg";

val bounded_packed_chars_historical_first_parse_cells_v =
  translate
    compute_boundedHistoricalDihedralFirstParseControlTheory.bounded_packed_chars_historical_first_parse_cells_def;
val bounded_packed_chars_historical_first_parse_control_v =
  translate
    compute_boundedHistoricalDihedralFirstParseControlTheory.bounded_packed_chars_historical_first_parse_control_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_historical_first_parse_control
         (String.explode payload)
    then TextIO.print "parsed\n"
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

Definition compute_bounded_historical_dihedral_first_parse_control_prog_def:
  compute_bounded_historical_dihedral_first_parse_control_prog = ^prog
End

val _ = export_theory ();
