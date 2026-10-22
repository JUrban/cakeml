(* CakeML translation of compact Taylor constant and coordinate leaves. *)
Theory compute_boundedTaylorBaseProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorMulProg compute_boundedTaylorBase

val _ = translation_extends "compute_boundedTaylorMulProg";

val bounded_interval64_zeros_v =
  translate compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def;
val bounded_interval64_nth_v =
  translate compute_boundedTaylorBaseTheory.bounded_interval64_nth_def;
val bounded_interval64_unit_vector_v =
  translate compute_boundedTaylorBaseTheory.bounded_interval64_unit_vector_def;
val bounded_taylor64_constant_v =
  translate compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def;
val bounded_taylor64_variable_v =
  translate compute_boundedTaylorBaseTheory.bounded_taylor64_variable_def;

val _ = export_theory ();
