(* Direct executable program for the genuine complete cell-0 gate. *)
Theory compute_boundedCase10173HistoricalCell0Prog
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase10173HistoricalCellProg
  compute_boundedCase10173HistoricalCell0Data

val _ = translation_extends "compute_boundedCase10173HistoricalCellProg";

val bounded_case10173_cell0_positive_interval_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_positive_interval_def;
val bounded_case10173_cell0_center_environment_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_environment_def;
val bounded_case10173_cell0_box_environment_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_environment_def;
val bounded_case10173_cell0_radii_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_radii_def;
val bounded_case10173_cell0_sqrt_certificates_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_sqrt_certificates_def;
val bounded_case10173_cell0_center_root_delta_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_root_delta_def;
val bounded_case10173_cell0_center_root_four_x0_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_root_four_x0_def;
val bounded_case10173_cell0_center_reciprocals_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_reciprocals_def;
val bounded_case10173_cell0_box_root_delta_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_root_delta_def;
val bounded_case10173_cell0_box_root_four_x0_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_root_four_x0_def;
val bounded_case10173_cell0_box_reciprocals_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_reciprocals_def;
val bounded_case10173_cell0_check_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_check_def;
val bounded_case10173_cell0_repeat_v =
  translate
    compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_repeat_def;

Quote main = cakeml:
  if bounded_case10173_cell0_check ()
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

Definition compute_bounded_case10173_historical_cell0_prog_def:
  compute_bounded_case10173_historical_cell0_prog = ^prog
End

val _ = export_theory ();
