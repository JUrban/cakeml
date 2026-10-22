(* CakeML translation of the exact decimal object-representation decoder. *)
Theory compute_boundedObjectDecimalDecodeProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCertificateDecimalProg compute_boundedObjectDecimalDecode

val _ = translation_extends "compute_boundedCertificateDecimalProg";

val _ = translate
  (bounded_object_decimal_signed64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (bounded_object_decimal_interval64_def
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
  (bounded_object_decimal_interval64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_decimal_interval64_list_ind_translation[local]:
  bounded_object_decimal_interval64_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_decimal_interval64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_decimal_interval64_list_ind_translation
  |> update_precondition;

val _ = export_theory ();
