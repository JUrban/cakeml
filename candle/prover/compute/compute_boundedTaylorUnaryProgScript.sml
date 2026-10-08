(* CakeML translation of the general compact unary Taylor chain rule. *)
Theory compute_boundedTaylorUnaryProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedAtanProg compute_boundedTaylorGradientProg
  compute_boundedTaylorUnary

val _ = translation_extends "compute_boundedAtanProg";

val bounded_interval64_self_outer_v =
  translate
    compute_boundedTaylorUnaryTheory.bounded_interval64_self_outer_def;
val bounded_taylor64_unary_complete_v =
  translate
    compute_boundedTaylorUnaryTheory.bounded_taylor64_unary_complete_def;

val _ = export_theory ();
