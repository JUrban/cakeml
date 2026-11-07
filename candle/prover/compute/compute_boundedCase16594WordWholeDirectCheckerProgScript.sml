(*****************************************************************************
 * Translation closure for the complete checker using direct topology.       *
 *                                                                           *
 * This deliberately extends the exact numerical runtime boundary, not the   *
 * generic pure-evaluator topology translation.                              *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectCheckerProg
Ancestors
  compute_boundedCase16594WordDirectTopologyProg
  compute_boundedCase16594WordWholeDirectChecker
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordDirectTopologyProg";

val _ = translate
  compute_boundedCase16594WordWholeDirectCheckerTheory.bounded_case16594_word_whole_direct_checker_def;

val _ = export_theory ();
