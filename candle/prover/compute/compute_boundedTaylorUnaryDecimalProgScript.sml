(* CakeML translation of the decimal unary compact-Taylor lift. *)
Theory compute_boundedTaylorUnaryDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorMulDecimalProg compute_boundedTaylorUnaryDecimal

val _ = translation_extends "compute_boundedTaylorMulDecimalProg";

val bounded_interval64_self_outer_decimal_v =
  translate
    compute_boundedTaylorUnaryDecimalTheory.bounded_interval64_self_outer_decimal_def;
val bounded_taylor64_unary_complete_decimal_v =
  translate
    compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_def;

val _ = export_theory ();
