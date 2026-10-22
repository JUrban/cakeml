(* CakeML translation of the compact six-dimensional Taylor state. *)
Theory compute_boundedTaylorStateProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedIntervalListProg compute_boundedTaylorState

val _ = translation_extends "compute_boundedIntervalListProg";

val bounded_taylor64_well_formed_v =
  translate compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def;
val bounded_taylor64_make_v =
  translate compute_boundedTaylorStateTheory.bounded_taylor64_make_def;
val bounded_taylor64_neg_v =
  translate compute_boundedTaylorStateTheory.bounded_taylor64_neg_def;
val bounded_taylor64_add_unchecked_v =
  translate
    compute_boundedTaylorStateTheory.bounded_taylor64_add_unchecked_def;
val bounded_taylor64_add_v =
  translate compute_boundedTaylorStateTheory.bounded_taylor64_add_def;

val _ = export_theory ();
