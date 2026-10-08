(* CakeML translation of checked compact Taylor square-root lifting. *)
Theory compute_boundedTaylorSqrtProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorInverseProg compute_boundedTaylorSqrt

val _ = translation_extends "compute_boundedTaylorInverseProg";

val bounded_taylor64_sqrt_v =
  translate compute_boundedTaylorSqrtTheory.bounded_taylor64_sqrt_def;

val _ = export_theory ();
