(* CakeML translation of signed 192-bit Taylor accumulation and rounding. *)
Theory compute_boundedWideSignedProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedWideProg compute_boundedWideSigned

val _ = translation_extends "compute_boundedWideProg";

val _ = register_type ``:bounded_signed192``;

val bounded192_is_zero_v =
  translate compute_boundedWideSignedTheory.bounded192_is_zero_def;
val bounded_signed192_make_v =
  translate compute_boundedWideSignedTheory.bounded_signed192_make_def;
val bounded_signed192_normalized_v =
  translate compute_boundedWideSignedTheory.bounded_signed192_normalized_def;
val bounded_signed192_add_v =
  translate compute_boundedWideSignedTheory.bounded_signed192_add_def;
val bounded_signed64_scale81_v =
  translate compute_boundedWideSignedTheory.bounded_signed64_scale81_def;
val bounded128_scale41_v =
  translate compute_boundedWideSignedTheory.bounded128_scale41_def;
val bounded192_shift_floor81_words_v =
  translate
    compute_boundedWideSignedTheory.bounded192_shift_floor81_words_def;
val bounded192_low81_nonzero_v =
  translate compute_boundedWideSignedTheory.bounded192_low81_nonzero_def;
val bounded_signed128_narrow64_option_v =
  translate
    compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def;
val bounded_signed192_shift_floor81_64_v =
  translate
    compute_boundedWideSignedTheory.bounded_signed192_shift_floor81_64_def;
val bounded_signed192_shift_ceil81_64_v =
  translate
    compute_boundedWideSignedTheory.bounded_signed192_shift_ceil81_64_def;

val _ = export_theory ();
