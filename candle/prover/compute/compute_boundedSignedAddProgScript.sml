(*
  CakeML translation of checked signed bounded accumulation.
*)
Theory compute_boundedSignedAddProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedSignedProg compute_boundedSignedAdd

val _ = translation_extends "compute_boundedSignedProg";

val bounded128_le_words_v =
  translate compute_boundedSignedAddTheory.bounded128_le_words_def;
val bounded_word64_sub_borrow_v =
  translate compute_boundedSignedAddTheory.bounded_word64_sub_borrow_def;
val bounded128_sub_words_v =
  translate compute_boundedSignedAddTheory.bounded128_sub_words_def;
val bounded_signed128_add_v =
  translate compute_boundedSignedAddTheory.bounded_signed128_add_def;

val _ = export_theory ();
