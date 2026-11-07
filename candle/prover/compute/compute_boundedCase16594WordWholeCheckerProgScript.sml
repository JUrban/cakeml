(*****************************************************************************
 * Standalone translation boundary for the complete case-16594 G5 checker. *
 *                                                                           *
 * This theory intentionally has no command-line main.  It first establishes *
 * the exact translation closure of the proved checker without committing to *
 * a compiler or runtime build.  The bounded G6 executable is added only once *
 * this parent identity and closure are green.                                *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeCheckerProg
Ancestors
  compute_boundedCase16594WordWholeTopologyBaseProg
  compute_boundedCase16594WordWholeChecker
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordWholeTopologyBaseProg";

val _ = translate
  compute_boundedCase16594WordWholeCheckerTheory.bounded_case16594_word_whole_checker_def;

val _ = export_theory ();
