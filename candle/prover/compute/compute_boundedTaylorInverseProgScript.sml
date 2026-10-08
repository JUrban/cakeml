(* CakeML translation of checked compact Taylor reciprocal lifting. *)
Theory compute_boundedTaylorInverseProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorUnaryProg compute_boundedTaylorInverse

val _ = translation_extends "compute_boundedTaylorUnaryProg";

val bounded_taylor64_inverse_v =
  translate compute_boundedTaylorInverseTheory.bounded_taylor64_inverse_def;

val _ = export_theory ();
