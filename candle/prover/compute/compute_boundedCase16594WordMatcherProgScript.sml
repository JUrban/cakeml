(*****************************************************************************
 * One-cell and complete 875-cell lockstep matchers.                         *
 *****************************************************************************)
Theory compute_boundedCase16594WordMatcherProg
Ancestors
  compute_boundedCase16594WordBytesProg
  compute_boundedCase16594WordWholeCellMatcher
  compute_boundedCase16594WordWholeCellsMatcher
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordBytesProg";

val _ = translate
  compute_boundedCase16594WordWholeCellMatcherTheory.bounded_case16594_word_whole_cell_match_def;
val _ = translate
  compute_boundedCase16594WordWholeCellsMatcherTheory.bounded_case16594_word_whole_cells_match_def;

val _ = export_theory ();
