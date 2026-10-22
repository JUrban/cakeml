(*
  Closed verified program for the first actual case16594 data-flow slice.
  It executes one genuine lower-coordinate product from every cell and checks
  both the authenticated fixture length and the complete result digest.
*)
Theory compute_boundedCase16594ActualProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedProg compute_boundedCase16594ActualData

val _ = translation_extends "compute_boundedProg";

val bounded_case16594_actual_lower_x1_x4_pairs_v =
  translate
    compute_boundedCase16594ActualDataTheory.bounded_case16594_actual_lower_x1_x4_pairs_def;
val bounded_case16594_actual_lower_x1_x4_digest_v =
  translate
    compute_boundedCase16594ActualDataTheory.bounded_case16594_actual_lower_x1_x4_digest_def;
val bounded_case16594_actual_lower_x1_x4_ok_v =
  translate
    compute_boundedCase16594ActualDataTheory.bounded_case16594_actual_lower_x1_x4_ok_def;

Quote main = cakeml:
  if bounded_case16594_actual_lower_x1_x4_ok () then () else raise Bind;
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

Definition compute_bounded_case16594_actual_prog_def:
  compute_bounded_case16594_actual_prog = ^prog
End

val _ = export_theory ();
