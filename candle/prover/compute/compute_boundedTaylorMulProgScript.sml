(* CakeML translation of checked compact Taylor multiplication. *)
Theory compute_boundedTaylorMulProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorAtanProg compute_boundedTaylorMul

val _ = translation_extends "compute_boundedTaylorAtanProg";

val bounded_interval64_symmetric_outer_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_symmetric_outer_def;
val bounded_taylor64_mul_v =
  translate compute_boundedTaylorMulTheory.bounded_taylor64_mul_def;

val _ = export_theory ();
