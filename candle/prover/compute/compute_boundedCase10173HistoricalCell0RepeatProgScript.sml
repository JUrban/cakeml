(* Development throughput harness for the genuine complete cell-0 gate. *)
Theory compute_boundedCase10173HistoricalCell0RepeatProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase10173HistoricalCell0Prog

val _ = translation_extends
  "compute_boundedCase10173HistoricalCell0Prog";

Quote main = cakeml:
  if bounded_case10173_cell0_repeat 4173
  then TextIO.print "accepted\n"
  else TextIO.print "rejected\n";
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

Definition compute_bounded_case10173_historical_cell0_repeat_prog_def:
  compute_bounded_case10173_historical_cell0_repeat_prog = ^prog
End

val _ = export_theory ();
