(* CakeML translation of exact stored interval negation and checked addition. *)
Theory compute_boundedIntervalAddProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedIntervalProg compute_boundedSignedEndpointAddProg
  compute_boundedIntervalAdd

val _ = translation_extends "compute_boundedIntervalProg";

val bounded_signed64_neg_v =
  translate
    compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def;
val bounded_signed64_add_v =
  translate
    compute_boundedSignedEndpointAddTheory.bounded_signed64_add_def;
val bounded_interval64_neg_v =
  translate compute_boundedIntervalAddTheory.bounded_interval64_neg_def;
val bounded_interval64_add_unchecked_v =
  translate
    compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def;
val bounded_interval64_add_v =
  translate compute_boundedIntervalAddTheory.bounded_interval64_add_def;

val _ = export_theory ();
