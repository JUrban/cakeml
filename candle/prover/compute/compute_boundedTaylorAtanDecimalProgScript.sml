(* CakeML translation of the decimal compact-Taylor arctangent lift. *)
Theory compute_boundedTaylorAtanDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedAtanDecimalProg compute_boundedTaylorAtanDecimal

val _ = translation_extends "compute_boundedAtanDecimalProg";

val bounded_taylor64_atan_decimal_v =
  translate
    compute_boundedTaylorAtanDecimalTheory.bounded_taylor64_atan_decimal_def;

val _ = export_theory ();
