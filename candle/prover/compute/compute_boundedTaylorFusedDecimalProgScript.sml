(* CakeML translation of decimal fused Taylor product normalization. *)
Theory compute_boundedTaylorFusedDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedObjectDecimalQProg compute_boundedTaylorMulProg
  compute_boundedTaylorFusedDecimal

val _ = translation_extends "compute_boundedTaylorMulProg";

(* The dyadic Taylor path normalizes wide values with word-level shifts and
 * therefore never needs the logical numeric projection at run time.  Decimal
 * normalization divides by 10^12, so make that projection executable at this
 * boundary rather than leaving an implicit untranslated dependency. *)
val bounded192_to_num_v =
  translate
    (compute_boundedTheory.bounded192_to_num_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);

(* Program translations have one linear executable environment even when the
 * HOL theory has several ancestors.  Install the decimal interval and
 * certificate operations on this Taylor chain so later product and unary
 * translations do not depend on a sibling environment merely being loaded. *)
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_product_mixed_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def;
val _ = translate
  compute_boundedCertificateDecimalTheory.bounded_decimal_scale_squared128_def;
val _ = translate
  compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_def;
val _ = translate
  compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_def;

val bounded192_floor64_decimal_v =
  translate
    (compute_boundedTaylorFusedDecimalTheory.bounded192_floor64_decimal_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val bounded192_ceil64_decimal_v =
  translate
    (compute_boundedTaylorFusedDecimalTheory.bounded192_ceil64_decimal_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val bounded_signed192_floor64_decimal_v =
  translate
    compute_boundedTaylorFusedDecimalTheory.bounded_signed192_floor64_decimal_def;
val bounded_signed192_ceil64_decimal_v =
  translate
    compute_boundedTaylorFusedDecimalTheory.bounded_signed192_ceil64_decimal_def;
val bounded_interval64_fused_products_decimal_v =
  translate
    compute_boundedTaylorFusedDecimalTheory.bounded_interval64_fused_products_decimal_def;

val _ = export_theory ();
