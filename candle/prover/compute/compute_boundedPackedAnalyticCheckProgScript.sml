(* CakeML translation of the program-parameterized packed analytic checker. *)
Theory compute_boundedPackedAnalyticCheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedPackedSequentialCase16594CheckProg
  compute_boundedPackedAnalyticCheck

val _ =
  translation_extends "compute_boundedPackedSequentialCase16594CheckProg";

val bounded_packed_chars_analytic_input_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_input_def;
val bounded_packed_chars_analytic_cell_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_cell_def;
val bounded_packed_chars_analytic_header_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_header_def;
val bounded_packed_analytic_result_accepts_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_analytic_result_accepts_def;
val bounded_packed_chars_analytic_eval_cell_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_eval_cell_def;
val bounded_packed_chars_analytic_check_cells_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_check_cells_def;
val bounded_packed_chars_analytic_complete_check_v =
  translate
    compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_complete_check_def;

val _ = export_theory ();
