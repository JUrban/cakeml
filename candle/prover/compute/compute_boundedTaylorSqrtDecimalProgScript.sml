(* CakeML translation of decimal reciprocal and square-root Taylor lifts. *)
Theory compute_boundedTaylorSqrtDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorUnaryDecimalProg compute_boundedCertificateDecimalProg
  compute_boundedTaylorSqrtDecimal

val _ = translation_extends "compute_boundedTaylorUnaryDecimalProg";

(* The strengthened source checker deliberately keeps these executable
 * predicates on the typed bounded carrier.  Their object-level counterparts
 * occur only in refinement theorems and must not enter the generated program. *)
val bounded_interval64_positive_inv_certificate_decimal_v =
  translate
    compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_def;
val bounded_interval64_positive_sqrt_certificate_decimal_v =
  translate
    compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_def;

val bounded_taylor64_inverse_decimal_v =
  translate
    compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_inverse_decimal_def;
val bounded_taylor64_sqrt_decimal_v =
  translate
    compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_def;

val _ = export_theory ();
