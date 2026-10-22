(* CakeML translation of word-only 192-bit Taylor operations. *)
Theory compute_boundedWideProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorStateProg compute_boundedWide

val _ = translation_extends "compute_boundedTaylorStateProg";

val bounded192_zero_v =
  translate compute_boundedWideTheory.bounded192_zero_def;
val bounded_word64_sub_borrow_in_v =
  translate compute_boundedWideTheory.bounded_word64_sub_borrow_in_def;
val bounded192_le_words_v =
  translate compute_boundedWideTheory.bounded192_le_words_def;
val bounded192_sub_words_v =
  translate compute_boundedWideTheory.bounded192_sub_words_def;
val bounded128_mul_word64_to_192_words_v =
  translate
    compute_boundedWideTheory.bounded128_mul_word64_to_192_words_def;

val _ = export_theory ();
