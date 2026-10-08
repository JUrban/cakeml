(* CakeML translation of the development-only first-cell state trace. *)
Theory compute_boundedCase16594StateTraceProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedPackedSequentialCase16594CheckProg
  compute_boundedCase16594StateTrace

val _ = translation_extends
  "compute_boundedPackedSequentialCase16594CheckProg";

val bounded_trace_word64_v =
  translate compute_boundedCase16594StateTraceTheory.bounded_trace_word64_def;
val bounded_signed64_trace_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_signed64_trace_hash_def;
val bounded_interval64_trace_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_interval64_trace_hash_def;
val bounded_interval64_list_trace_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_interval64_list_trace_hash_def;
val bounded_taylor64_trace_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_taylor64_trace_hash_def;
val bounded_taylor64_list_trace_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_taylor64_list_trace_hash_def;
val bounded_taylor64_stack_trace_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_taylor64_stack_trace_hash_def;
val bounded_case16594_instruction82_group_status_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_case16594_instruction82_group_status_def;
val bounded_case16594_instruction82_hessian_hash_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_case16594_instruction82_hessian_hash_def;
val bounded_case16594_instruction82_hessian_first_mismatch_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_case16594_instruction82_hessian_first_mismatch_def;
val bounded_case16594_first_native_trace_expected_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_case16594_first_native_trace_expected_def;
val bounded_case16594_state_trace_run_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_case16594_state_trace_run_def;
val bounded_case16594_first_state_trace_status_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_case16594_first_state_trace_status_def;
val bounded_packed_chars_case16594_first_state_trace_status_v =
  translate
    compute_boundedCase16594StateTraceTheory.bounded_packed_chars_case16594_first_state_trace_status_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
    val status = bounded_packed_chars_case16594_first_state_trace_status
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

Definition compute_bounded_case16594_state_trace_prog_def:
  compute_bounded_case16594_state_trace_prog = ^prog
End

val _ = export_theory ();
