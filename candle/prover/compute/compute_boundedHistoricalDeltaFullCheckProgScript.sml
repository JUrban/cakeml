(* CakeML translation of the complete 4,173-cell historical delta gate. *)
Theory compute_boundedHistoricalDeltaFullCheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedHistoricalDeltaPackedCheckProg
  compute_boundedHistoricalDeltaFullCheck

val _ = translation_extends "compute_boundedHistoricalDeltaPackedCheckProg";

val bounded_packed_chars_historical_delta_full_header_v =
  translate
    compute_boundedHistoricalDeltaFullCheckTheory.bounded_packed_chars_historical_delta_full_header_def;
val bounded_packed_chars_historical_delta_full_check_v =
  translate
    compute_boundedHistoricalDeltaFullCheckTheory.bounded_packed_chars_historical_delta_full_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_historical_delta_full_check
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

Definition compute_bounded_historical_delta_full_check_prog_def:
  compute_bounded_historical_delta_full_check_prog = ^prog
End

val _ = export_theory ();
