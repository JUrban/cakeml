(*
  CakeML translation of the proved signed, directed shift-40 endpoint layer.
*)
Theory compute_boundedSignedProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedProg compute_boundedSigned

val _ = translation_extends "compute_boundedProg";

val _ = register_type ``:bounded_signed64``;
val _ = register_type ``:bounded_signed128``;

val bounded128_is_zero_v =
  translate compute_boundedSignedTheory.bounded128_is_zero_def;
val bounded_signed128_make_v =
  translate compute_boundedSignedTheory.bounded_signed128_make_def;
val bounded_signed128_negative_v =
  translate compute_boundedSignedTheory.bounded_signed128_negative_def;
val bounded_signed128_magnitude_v =
  translate compute_boundedSignedTheory.bounded_signed128_magnitude_def;
val bounded_word64_low40_nonzero_v =
  translate compute_boundedSignedTheory.bounded_word64_low40_nonzero_def;
val bounded_word64_mul_shift_ceil40_v =
  translate compute_boundedSignedTheory.bounded_word64_mul_shift_ceil40_def;
val bounded_signed_word64_mul_floor40_v =
  translate compute_boundedSignedTheory.bounded_signed_word64_mul_floor40_def;
val bounded_signed_word64_mul_ceil40_v =
  translate compute_boundedSignedTheory.bounded_signed_word64_mul_ceil40_def;

val _ = export_theory ();
