(* CakeML translation of the sequential external nonlinear-input parser. *)
Theory compute_boundedPackedSequentialInputProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedPackedInputProg compute_boundedPackedSequentialInput

val _ = translation_extends "compute_boundedPackedInputProg";

val bounded_packed_chars_word64_aux_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_aux_def;
val bounded_packed_chars_signed64_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_def;
val bounded_packed_chars_interval64_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_interval64_def;
val bounded_packed_chars_positive_interval64_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_positive_interval64_def;
val bounded_packed_chars_positive_interval64_list_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_positive_interval64_list_def;
val bounded_packed_chars_word64_list_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_list_def;
val bounded_packed_chars_signed64_list_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_list_def;
val bounded_packed_chars_case16594_input_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_input_def;
val bounded_packed_chars_analytic64_certificate_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_analytic64_certificate_def;
val bounded_packed_chars_analytic64_certificate_list_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_analytic64_certificate_list_def;
val bounded_packed_chars_case16594_cell_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_cell_def;
val bounded_packed_chars_case16594_cells_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_cells_def;
val bounded_packed_chars_prefix_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_prefix_def;
val bounded_packed_chars_case16594_header_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_header_def;
val bounded_packed_chars_case16594_payload_ok_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_payload_ok_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_case16594_payload_ok (String.explode payload) then
      TextIO.print "accepted\n"
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

Definition compute_bounded_packed_sequential_case16594_prog_def:
  compute_bounded_packed_sequential_case16594_prog = ^prog
End

val _ = export_theory ();
