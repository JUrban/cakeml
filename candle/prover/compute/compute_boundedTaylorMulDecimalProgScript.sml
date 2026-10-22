(* CakeML translation of complete decimal compact-Taylor multiplication. *)
Theory compute_boundedTaylorMulDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorCompleteDecimalProg compute_boundedTaylorMulDecimal

val _ = translation_extends "compute_boundedTaylorCompleteDecimalProg";

val bounded_taylor64_mul_decimal_v =
  translate
    compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_def;

val _ = export_theory ();
