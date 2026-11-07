(*****************************************************************************
 * Saved translation boundary for the case-16594 whole topology call.       *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeTopologyBaseProg
Ancestors
  compute_boundedCase16594WordWholeHolLightCeqsProg
  compute_boundedCase16594WordWholeChecker
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordWholeHolLightCeqsProg";

fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

val _ = translate_closed
  compute_boundedCase16594WordWholeCheckerTheory.bounded_case16594_word_topology_fuel_def;
val _ = translate
  compute_boundedCase16594Cell0WholeCombinedEntryTheory.bounded_case16594_cell0_whole_combined_ceqs_def;
val _ = translate
  compute_boundedCase16594WordWholeCheckerTheory.bounded_case16594_word_topology_expression_def;

val _ = export_theory ();
