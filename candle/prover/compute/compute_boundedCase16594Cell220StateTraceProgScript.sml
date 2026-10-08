(* CakeML translation of the cell-220 instruction-state discriminator. *)
Theory compute_boundedCase16594Cell220StateTraceProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase16594StateTraceProg
  compute_boundedCase16594Cell220StateTrace

val _ = translation_extends "compute_boundedCase16594StateTraceProg";

val bounded_case16594_cell220_native_trace_expected_v =
  translate
    compute_boundedCase16594Cell220StateTraceTheory.bounded_case16594_cell220_native_trace_expected_def;
val bounded_case16594_cell220_trace_run_v =
  translate
    compute_boundedCase16594Cell220StateTraceTheory.bounded_case16594_cell220_trace_run_def;
val bounded_packed_chars_case16594_cell_at_v =
  translate
    compute_boundedCase16594Cell220StateTraceTheory.bounded_packed_chars_case16594_cell_at_def;
val bounded_case16594_cell220_state_trace_status_v =
  translate
    compute_boundedCase16594Cell220StateTraceTheory.bounded_case16594_cell220_state_trace_status_def;
val bounded_packed_chars_case16594_cell220_state_trace_status_v =
  translate
    compute_boundedCase16594Cell220StateTraceTheory.bounded_packed_chars_case16594_cell220_state_trace_status_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
    val status = bounded_packed_chars_case16594_cell220_state_trace_status
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

Definition compute_bounded_case16594_cell220_state_trace_prog_def:
  compute_bounded_case16594_cell220_state_trace_prog = ^prog
End

val _ = export_theory ();
