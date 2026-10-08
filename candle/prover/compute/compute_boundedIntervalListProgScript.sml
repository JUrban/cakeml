(* CakeML translation of shape-safe fixed-width interval-list operations. *)
Theory compute_boundedIntervalListProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedIntervalAddProg compute_boundedIntervalList

val _ = translation_extends "compute_boundedIntervalAddProg";

val bounded_interval64_zero_v =
  translate compute_boundedIntervalListTheory.bounded_interval64_zero_def;
val bounded_interval64_is_zero_v =
  translate compute_boundedIntervalListTheory.bounded_interval64_is_zero_def;
val bounded_interval64_list_valid_v =
  translate compute_boundedIntervalListTheory.bounded_interval64_list_valid_def;
val bounded_interval64_list_neg_v =
  translate compute_boundedIntervalListTheory.bounded_interval64_list_neg_def;
val bounded_interval64_list_add_v =
  translate compute_boundedIntervalListTheory.bounded_interval64_list_add_def;
val bounded_interval64_list_scale_v =
  translate compute_boundedIntervalListTheory.bounded_interval64_list_scale_def;
val bounded_interval64_list_pairwise_mul_v =
  translate
    compute_boundedIntervalListTheory.bounded_interval64_list_pairwise_mul_def;

val _ = export_theory ();
