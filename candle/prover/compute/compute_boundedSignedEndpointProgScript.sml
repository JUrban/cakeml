(* CakeML translation of checked one-word signed endpoint operations. *)
Theory compute_boundedSignedEndpointProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedSignedAddProg compute_boundedSignedEndpoint

val _ = translation_extends "compute_boundedSignedAddProg";

val bounded_signed64_make_v =
  translate compute_boundedSignedEndpointTheory.bounded_signed64_make_def;
val bounded_signed64_widen128_v =
  translate
    compute_boundedSignedEndpointTheory.bounded_signed64_widen128_def;
val bounded_signed128_narrow64_v =
  translate
    compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_def;
val bounded_signed64_effective_negative_v =
  translate
    compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def;
val bounded_signed64_magnitude_v =
  translate
    compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def;
val bounded_signed64_le_v =
  translate compute_boundedSignedEndpointTheory.bounded_signed64_le_def;
val bounded_signed64_min_v =
  translate compute_boundedSignedEndpointTheory.bounded_signed64_min_def;
val bounded_signed64_max_v =
  translate compute_boundedSignedEndpointTheory.bounded_signed64_max_def;

val _ = export_theory ();
