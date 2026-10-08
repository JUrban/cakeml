(* CakeML translation of the development-only complete-batch localizer. *)
Theory compute_boundedCase16594BatchStatusProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedPackedSequentialCase16594CheckProg
  compute_boundedCase16594BatchStatus

val _ = translation_extends
  "compute_boundedPackedSequentialCase16594CheckProg";

val bounded_packed_chars_case16594_batch_status_aux_v =
  translate
    compute_boundedCase16594BatchStatusTheory.bounded_packed_chars_case16594_batch_status_aux_def;
val bounded_packed_chars_case16594_batch_status_v =
  translate
    compute_boundedCase16594BatchStatusTheory.bounded_packed_chars_case16594_batch_status_def;
val bounded_packed_chars_case16594_batch_status_select_v =
  translate
    compute_boundedCase16594BatchStatusTheory.bounded_packed_chars_case16594_batch_status_select_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
    val status = bounded_packed_chars_case16594_batch_status_select
      (String.explode payload)
  in
    TextIO.output1 TextIO.stdOut (Char.chr (Word8.toInt status))
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

Definition compute_bounded_case16594_batch_status_prog_def:
  compute_bounded_case16594_batch_status_prog = ^prog
End

val _ = export_theory ();
