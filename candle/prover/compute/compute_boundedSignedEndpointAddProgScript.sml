(* CakeML translation of exact stored signed endpoint negation and addition. *)
Theory compute_boundedSignedEndpointAddProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedSignedEndpointProg compute_boundedSignedEndpointAdd

val _ = translation_extends "compute_boundedSignedEndpointProg";

val bounded_signed64_neg_v =
  translate
    compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def;
val bounded_signed64_add_v =
  translate
    compute_boundedSignedEndpointAddTheory.bounded_signed64_add_def;

val _ = export_theory ();
