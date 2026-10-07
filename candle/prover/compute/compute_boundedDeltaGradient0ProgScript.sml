(*
  Closed verified program for component zero of grad(delta) over every one of
  the 875 authenticated case16594 boxes.  This extends the already translated
  complete input image; it does not duplicate or regenerate the fixture.
*)
Theory compute_boundedDeltaGradient0Prog
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedCase16594InputProg compute_boundedDeltaGradient0

val _ = translation_extends "compute_boundedCase16594InputProg";

val _ = register_type ``:bounded_signed64``;
val _ = register_type ``:bounded_signed128``;

(* The input image extends compute_boundedProg rather than the independent
   signed translation state, so translate the small signed support layer into
   this state exactly once. *)
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

val bounded128_le_words_v =
  translate compute_boundedSignedAddTheory.bounded128_le_words_def;
val bounded_word64_sub_borrow_v =
  translate compute_boundedSignedAddTheory.bounded_word64_sub_borrow_def;
val bounded128_sub_words_v =
  translate compute_boundedSignedAddTheory.bounded128_sub_words_def;
val bounded_signed128_add_v =
  translate compute_boundedSignedAddTheory.bounded_signed128_add_def;

val bounded_signed128_zero_v =
  translate compute_boundedDeltaGradient0Theory.bounded_signed128_zero_def;
val bounded_signed128_neg_v =
  translate compute_boundedDeltaGradient0Theory.bounded_signed128_neg_def;
val bounded_signed128_sum_aux_v =
  translate compute_boundedDeltaGradient0Theory.bounded_signed128_sum_aux_def;
val bounded_signed128_sum_v =
  translate compute_boundedDeltaGradient0Theory.bounded_signed128_sum_def;
val bounded_positive_interval_mul_v =
  translate compute_boundedDeltaGradient0Theory.bounded_positive_interval_mul_def;
val bounded_positive_interval_products_v =
  translate compute_boundedDeltaGradient0Theory.bounded_positive_interval_products_def;
val bounded_delta_gradient0_from_products_v =
  translate compute_boundedDeltaGradient0Theory.bounded_delta_gradient0_from_products_def;
val bounded_delta_gradient0_box_v =
  translate compute_boundedDeltaGradient0Theory.bounded_delta_gradient0_box_def;
val bounded_signed128_digest_v =
  translate compute_boundedDeltaGradient0Theory.bounded_signed128_digest_def;
val bounded_delta_gradient0_batch_v =
  translate compute_boundedDeltaGradient0Theory.bounded_delta_gradient0_batch_def;
val bounded_delta_gradient0_complete_ok_v =
  translate compute_boundedDeltaGradient0Theory.bounded_delta_gradient0_complete_ok_def;

Quote main = cakeml:
  if bounded_delta_gradient0_complete_ok () then () else raise Bind;
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_bounded_delta_gradient0_prog_def:
  compute_bounded_delta_gradient0_prog = ^prog
End

val _ = export_theory ();
