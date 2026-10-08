(* CakeML translation of the development source-DAG complete checker. *)
Theory compute_boundedPackedSourceDagCase16594CheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase16594SourceDagEvalProg
  compute_boundedPackedSourceDagCase16594Check

val _ = translation_extends "compute_boundedCase16594SourceDagEvalProg";

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

val bounded_packed_source_dag_case16594_result_accepts_v =
  translate
    compute_boundedPackedSourceDagCase16594CheckTheory.bounded_packed_source_dag_case16594_result_accepts_def;
val bounded_packed_chars_source_dag_case16594_eval_cell_v =
  translate
    compute_boundedPackedSourceDagCase16594CheckTheory.bounded_packed_chars_source_dag_case16594_eval_cell_def;
val bounded_packed_chars_source_dag_case16594_check_cells_v =
  translate
    compute_boundedPackedSourceDagCase16594CheckTheory.bounded_packed_chars_source_dag_case16594_check_cells_def;
val bounded_packed_chars_source_dag_case16594_complete_check_v =
  translate
    compute_boundedPackedSourceDagCase16594CheckTheory.bounded_packed_chars_source_dag_case16594_complete_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_source_dag_case16594_complete_check
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

Definition compute_bounded_packed_source_dag_case16594_check_prog_def:
  compute_bounded_packed_source_dag_case16594_check_prog = ^prog
End

val _ = export_theory ();
