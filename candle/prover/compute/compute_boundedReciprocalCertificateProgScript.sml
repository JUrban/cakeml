(* CakeML translation of checked fixed-scale reciprocal certificates. *)
Theory compute_boundedReciprocalCertificateProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedSqrtCertificateProg compute_boundedReciprocalCertificate

val _ = translation_extends "compute_boundedSqrtCertificateProg";

val bounded_signed64_strict_positive_v =
  translate
    compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def;
val bounded_signed64_strict_negative_v =
  translate
    compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def;
val bounded_scale_squared128_v =
  translate
    compute_boundedReciprocalCertificateTheory.bounded_scale_squared128_def;
val bounded_interval64_inv_certificate_v =
  translate
    compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def;

val _ = export_theory ();
