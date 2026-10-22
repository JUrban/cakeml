(* CakeML translation of checked compact Taylor multiplication. *)
Theory compute_boundedTaylorMulProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorAtanProg compute_boundedTaylorMul

val _ = translation_extends "compute_boundedTaylorAtanProg";

val bounded_signed64_raw_product_v =
  translate compute_boundedTaylorMulTheory.bounded_signed64_raw_product_def;
val bounded_signed128_le_words_v =
  translate compute_boundedTaylorMulTheory.bounded_signed128_le_words_def;
val bounded_signed128_min_v =
  translate compute_boundedTaylorMulTheory.bounded_signed128_min_def;
val bounded_signed128_max_v =
  translate compute_boundedTaylorMulTheory.bounded_signed128_max_def;
val bounded_interval64_raw_product_from_pairs_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_raw_product_from_pairs_def;
val bounded_interval64_raw_product_mixed_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_raw_product_mixed_def;
val bounded_interval64_raw_mul_bounds_unchecked_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_unchecked_def;
val bounded_signed128_widen192_v =
  translate compute_boundedTaylorMulTheory.bounded_signed128_widen192_def;
val bounded_interval64_raw_sum_acc_v =
  translate compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def;
val bounded192_shift_floor40_128_v =
  translate compute_boundedTaylorMulTheory.bounded192_shift_floor40_128_def;
val bounded192_low40_nonzero_v =
  translate compute_boundedTaylorMulTheory.bounded192_low40_nonzero_def;
val bounded_signed192_shift_floor40_64_v =
  translate
    compute_boundedTaylorMulTheory.bounded_signed192_shift_floor40_64_def;
val bounded_signed192_shift_ceil40_64_v =
  translate
    compute_boundedTaylorMulTheory.bounded_signed192_shift_ceil40_64_def;
val bounded_interval64_fused_products_v =
  translate compute_boundedTaylorMulTheory.bounded_interval64_fused_products_def;
val bounded_interval64_fused_scale_add_v =
  translate compute_boundedTaylorMulTheory.bounded_interval64_fused_scale_add_def;
val bounded_interval64_symmetric_product_pairs_row_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_row_def;
val bounded_interval64_symmetric_product_pairs_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_def;
val bounded_interval64_fused_hessian_v =
  translate compute_boundedTaylorMulTheory.bounded_interval64_fused_hessian_def;
val bounded_interval64_symmetric_outer_v =
  translate
    compute_boundedTaylorMulTheory.bounded_interval64_symmetric_outer_def;
val bounded_taylor64_mul_v =
  translate compute_boundedTaylorMulTheory.bounded_taylor64_mul_def;

val _ = export_theory ();
