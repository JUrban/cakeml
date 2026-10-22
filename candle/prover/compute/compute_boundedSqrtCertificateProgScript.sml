(* CakeML translation of checked fixed-scale square-root certificates. *)
Theory compute_boundedSqrtCertificateProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorGradientProg compute_boundedSqrtCertificate

val _ = translation_extends "compute_boundedTaylorGradientProg";

val bounded_interval64_sqrt_certificate_v =
  translate
    compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_def;

val _ = export_theory ();
