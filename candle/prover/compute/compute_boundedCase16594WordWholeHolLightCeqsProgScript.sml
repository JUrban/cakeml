(*****************************************************************************
 * Small ordinary HOL Light whole-call equation suffix for the G6 checker.  *
 *                                                                           *
 * The 840-equation numerical dispatcher is already translated by the       *
 * runtime parent.  Keeping this nine-equation suffix in its own saved       *
 * translation avoids re-expanding the complete combined environment in     *
 * every final-checker edit.                                                  *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeHolLightCeqsProg
Ancestors
  compute_boundedCase16594WordRuntimeProg
  compute_boundedCase16594Cell0WholeHolLightData
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase16594WordRuntimeProg";

fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

val _ = translate_closed
  compute_boundedCase16594Cell0WholeHolLightDataTheory.bounded_case16594_cell0_whole_hol_light_ceqs_def;

val _ = export_theory ();
