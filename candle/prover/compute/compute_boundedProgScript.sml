(*
  Translation boundary for the experimental bounded compute primitives.
*)
Theory compute_boundedProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  basisProg compute_bounded

val _ = translation_extends "basisProg";

val _ = register_type ``:bounded128``;
val _ = register_type ``:bounded192``;

val bounded_word64_add_carry_v =
  translate compute_boundedTheory.bounded_word64_add_carry_def;
val bounded_word64_mul_full_num_v =
  translate compute_boundedTheory.bounded_word64_mul_full_num_def;
val bounded_word64_mul_full_chunks22_v =
  translate compute_boundedTheory.bounded_word64_mul_full_chunks22_def;
val bounded_word64_mul_shift_floor40_v =
  translate compute_boundedTheory.bounded_word64_mul_shift_floor40_def;
val bounded_word64_mul_shift_floor40_repeat_v =
  translate compute_boundedTheory.bounded_word64_mul_shift_floor40_repeat_def;
val bounded_word64_mul_shift_floor40_pairs_v =
  translate compute_boundedTheory.bounded_word64_mul_shift_floor40_pairs_def;
val bounded128_shift_floor40_words_v =
  translate compute_boundedTheory.bounded128_shift_floor40_words_def;
val bounded128_shift_floor40_repeat_v =
  translate compute_boundedTheory.bounded128_shift_floor40_repeat_def;
val bounded_word64_mul_full_repeat_v =
  translate compute_boundedTheory.bounded_word64_mul_full_repeat_def;
val bounded_word64_mul_chunks22_repeat_v =
  translate compute_boundedTheory.bounded_word64_mul_chunks22_repeat_def;
val bounded_word64_mul_repeat_control_v =
  translate compute_boundedTheory.bounded_word64_mul_repeat_control_def;
val bounded128_add_words_v =
  translate compute_boundedTheory.bounded128_add_words_def;
val bounded128_add_words_repeat_v =
  translate compute_boundedTheory.bounded128_add_words_repeat_def;
val bounded128_repeat_control_v =
  translate compute_boundedTheory.bounded128_repeat_control_def;
val bounded192_add_words_v =
  translate compute_boundedTheory.bounded192_add_words_def;
val bounded192_add_words_repeat_v =
  translate compute_boundedTheory.bounded192_add_words_repeat_def;
val bounded_sign_class_dispatch_v =
  translate compute_boundedTheory.bounded_sign_class_dispatch_def;
val bounded_sign_class_repeat_v =
  translate compute_boundedTheory.bounded_sign_class_repeat_def;
val bounded_boolean_branch_repeat_v =
  translate compute_boundedTheory.bounded_boolean_branch_repeat_def;
val bounded_narrow_trace_repeat_v =
  translate compute_boundedTheory.bounded_narrow_trace_repeat_def;

val _ = export_theory ();
