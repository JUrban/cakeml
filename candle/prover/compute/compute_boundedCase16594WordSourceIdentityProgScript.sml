(*****************************************************************************
 * Literal approved identities for the exact 167-action source prefix.      *
 *****************************************************************************)
Theory compute_boundedCase16594WordSourceIdentityProg
Ancestors
  compute_boundedCase16594WordMatcherProg
  compute_boundedCase16594ObjectDispatchJointCompleteInvariant
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase16594WordMatcherProg";

fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

val _ = translate_closed
  compute_boundedCase16594ObjectDispatchJointCompleteInvariantTheory.bounded_case16594_generic_prefix167_codes_cv_def;
val _ = translate_closed
  compute_boundedCase16594ObjectDispatchJointCompleteInvariantTheory.bounded_case16594_generic_prefix167_sources_cv_def;

val _ = export_theory ();
