(* CakeML translation of the one-cell second-order discriminator. *)
Theory compute_boundedHistoricalDihedralSecondStatusProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedHistoricalDihedralSecondPackedCheckProg
  compute_boundedHistoricalDihedralSecondStatus

val _ = translation_extends
  "compute_boundedHistoricalDihedralSecondPackedCheckProg";

val bounded_historical_dihedral_second_certificate_stage_v =
  translate
    compute_boundedHistoricalDihedralSecondStatusTheory.bounded_historical_dihedral_second_certificate_stage_def;
val bounded_packed_historical_second_cell_status_v =
  translate
    compute_boundedHistoricalDihedralSecondStatusTheory.bounded_packed_historical_second_cell_status_def;
val bounded_packed_chars_historical_second_status_v =
  translate
    compute_boundedHistoricalDihedralSecondStatusTheory.bounded_packed_chars_historical_second_status_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
    val status = bounded_packed_chars_historical_second_status
      (String.explode payload)
  in
    TextIO.print (Int.toString status);
    TextIO.print "\n"
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

Definition compute_bounded_historical_dihedral_second_status_prog_def:
  compute_bounded_historical_dihedral_second_status_prog = ^prog
End

val _ = export_theory ();
