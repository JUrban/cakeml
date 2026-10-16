(* CakeML translation of decimal compact-Taylor product-rule building blocks. *)
Theory compute_boundedTaylorProductDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorFusedDecimalProg compute_boundedIntervalDecimalProg
  compute_boundedTaylorProductDecimal

val _ = translation_extends "compute_boundedTaylorFusedDecimalProg";

val bounded_interval64_list_scale_decimal_v =
  translate
    compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def;
val bounded_interval64_fused_scale_add_decimal_v =
  translate
    compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_scale_add_decimal_def;
val bounded_interval64_fused_hessian_decimal_v =
  translate
    compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def;
val bounded_interval64_symmetric_outer_decimal_v =
  translate
    compute_boundedTaylorProductDecimalTheory.bounded_interval64_symmetric_outer_decimal_def;

val _ = export_theory ();
