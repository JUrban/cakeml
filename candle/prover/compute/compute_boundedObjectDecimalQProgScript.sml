(* CakeML translation of authenticated positive rational-box conversion to
 * the decimal fixed-scale intervals consumed by the nonlinear checker. *)
Theory compute_boundedObjectDecimalQProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedObjectDecimalDecodeProg compute_boundedObjectDecimalQ

val _ = translation_extends "compute_boundedObjectDecimalDecodeProg";

val _ = translate
  (bounded_decimal_natural_floor64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (bounded_decimal_natural_ceil64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate bounded_object_positive_q_floor64_decimal_def;

Theorem bounded_object_positive_q_floor64_decimal_side_total[local]:
  !encoded. bounded_object_positive_q_floor64_decimal_side encoded
Proof
  rw [fetch "-" "bounded_object_positive_q_floor64_decimal_side_def",
      fetch "-" "bounded_decimal_natural_floor64_side_def"]
QED

val _ = bounded_object_positive_q_floor64_decimal_side_total
  |> update_precondition;

val _ = translate bounded_object_positive_q_ceil64_decimal_def;

Theorem bounded_object_positive_q_ceil64_decimal_side_total[local]:
  !encoded. bounded_object_positive_q_ceil64_decimal_side encoded
Proof
  rw [fetch "-" "bounded_object_positive_q_ceil64_decimal_side_def",
      fetch "-" "bounded_decimal_natural_ceil64_side_def"]
QED

val _ = bounded_object_positive_q_ceil64_decimal_side_total
  |> update_precondition;

val _ = translate
  (bounded_object_positive_q_interval64_decimal_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_tail_induction[local]:
  !P. (!v:cv. (!x y. v = Pair x y ==> P y) ==> P v) ==> !v. P v
Proof
  gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

val _ = translate_no_ind
  (bounded_object_positive_q_interval64_decimal_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_positive_q_interval64_decimal_list_ind_translation[local]:
  bounded_object_positive_q_interval64_decimal_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_positive_q_interval64_decimal_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_positive_q_interval64_decimal_list_ind_translation
  |> update_precondition;

val _ = export_theory ();
