(* CakeML translation of the streaming complete case16594 checker. *)
Theory compute_boundedPackedSequentialCase16594CheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase16594PreparedPlanProg
  compute_boundedPackedSequentialCase16594Check

val _ = translation_extends "compute_boundedCase16594PreparedPlanProg";

val bounded_packed_interval64_zero_v =
  translate compute_boundedPackedInputTheory.bounded_packed_interval64_zero_def;
val bounded_packed_chars_word64_aux_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_aux_def;
val bounded_packed_chars_signed64_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_def;
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
val bounded_packed_chars_prefix_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_prefix_def;
val bounded_packed_chars_case16594_header_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_case16594_header_def;

val bounded_packed_case16594_result_accepts_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_case16594_result_accepts_def;
val bounded_packed_chars_case16594_eval_cell_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_eval_cell_def;
val bounded_packed_chars_case16594_check_cells_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_check_cells_def;
val bounded_packed_chars_case16594_complete_check_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_complete_check_def;
val bounded_packed_chars_case16594_cell_status_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_cell_status_def;
val bounded_packed_chars_case16594_first_status_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_first_status_def;
val bounded_packed_chars_case16594_cell_status8_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_cell_status8_def;
val bounded_packed_chars_case16594_first_status8_v =
  translate
    compute_boundedPackedSequentialCase16594CheckTheory.bounded_packed_chars_case16594_first_status8_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    let
      val bytes = String.explode payload
    in
      if bounded_packed_chars_case16594_complete_check bytes then
        TextIO.print "accepted\n"
      else
        let
          val status = bounded_packed_chars_case16594_first_status8 bytes
        in
          if status = Word8.fromInt 0 then TextIO.print "rejected:header\n"
          else if status = Word8.fromInt 1 then TextIO.print "rejected:first-parse\n"
          else if status = Word8.fromInt 2 then TextIO.print "rejected:first-eval\n"
          else if status = Word8.fromInt 3 then TextIO.print "rejected:first-domain\n"
          else if status = Word8.fromInt 4 then TextIO.print "rejected:after-first\n"
          else TextIO.print "rejected:first-bound\n"
        end
    end
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

Definition compute_bounded_packed_sequential_case16594_check_prog_def:
  compute_bounded_packed_sequential_case16594_check_prog = ^prog
End

val _ = export_theory ();
