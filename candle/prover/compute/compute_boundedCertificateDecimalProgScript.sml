(* CakeML translation of checked decimal fixed-scale certificates. *)
Theory compute_boundedCertificateDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedIntervalDecimalProg compute_boundedCertificateDecimal

val _ = translation_extends "compute_boundedIntervalDecimalProg";

(* These scale-independent helpers are not part of the smaller interval
 * translator ancestry, so install their existing proved definitions once. *)
val bounded_word64_product128_decimal_support_v =
  translate compute_boundedTaylorCompleteTheory.bounded_word64_product128_def;
val bounded_signed64_strict_positive_decimal_support_v =
  translate
    compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def;
val bounded_signed64_strict_negative_decimal_support_v =
  translate
    compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def;

val bounded_decimal_scale_squared128_v =
  translate
    compute_boundedCertificateDecimalTheory.bounded_decimal_scale_squared128_def;
val bounded_interval64_sqrt_certificate_decimal_v =
  translate
    compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_def;
val bounded_interval64_inv_certificate_decimal_v =
  translate
    compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_def;

val _ = export_theory ();
