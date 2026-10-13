(* Kernel-lineage checkpoint for reachable interval and wide arithmetic. *)
Theory compute_candleKernelBoundedPacketIntervalProg
Ancestors
  compute_candleKernelBoundedPacketSignedProg
  compute_boundedInterval compute_boundedIntervalAdd
  compute_boundedIntervalList compute_boundedTaylorState
  compute_boundedWide compute_boundedWideSigned
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends
  "compute_candleKernelBoundedPacketSignedProg";

val _ = register_type ``:bounded_interval64``;

val _ = translate compute_boundedIntervalTheory.bounded_interval64_lower_def;
val _ = translate compute_boundedIntervalTheory.bounded_interval64_upper_def;
val _ = translate compute_boundedIntervalTheory.bounded_signed64_nonnegative_def;
val _ = translate compute_boundedIntervalTheory.bounded_signed64_nonpositive_def;
val _ = translate compute_boundedIntervalTheory.bounded_scaled_mul_floor64_def;
val _ = translate compute_boundedIntervalTheory.bounded_scaled_mul_ceil64_def;
val _ = translate compute_boundedIntervalTheory.bounded_interval64_product_from_pairs_def;
val _ = translate compute_boundedIntervalTheory.bounded_interval64_product_mixed_def;
val _ = translate compute_boundedIntervalTheory.bounded_interval64_mul_unchecked_def;
val _ = translate compute_boundedIntervalTheory.bounded_interval64_valid_def;
val _ = translate compute_boundedIntervalTheory.bounded_interval64_mul_def;

val _ = translate compute_boundedIntervalAddTheory.bounded_interval64_neg_def;
val _ = translate compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def;
val _ = translate compute_boundedIntervalAddTheory.bounded_interval64_add_def;

val _ = translate compute_boundedIntervalListTheory.bounded_interval64_zero_def;
val _ = translate compute_boundedIntervalListTheory.bounded_interval64_list_valid_def;
val _ = translate compute_boundedIntervalListTheory.bounded_interval64_list_add_def;
val _ = translate compute_boundedIntervalListTheory.bounded_interval64_list_scale_def;
val _ = translate compute_boundedIntervalListTheory.bounded_interval64_list_pairwise_mul_def;

val _ = translate compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def;
val _ = translate compute_boundedTaylorStateTheory.bounded_taylor64_make_def;
val _ = translate compute_boundedTaylorStateTheory.bounded_taylor64_add_unchecked_def;
val _ = translate compute_boundedTaylorStateTheory.bounded_taylor64_add_def;

val _ = translate compute_boundedWideTheory.bounded192_zero_def;
val _ = translate compute_boundedWideTheory.bounded_word64_sub_borrow_in_def;
val _ = translate compute_boundedWideTheory.bounded192_le_words_def;
val _ = translate compute_boundedWideTheory.bounded192_sub_words_def;
val _ = translate compute_boundedWideTheory.bounded128_mul_word64_to_192_words_def;

val _ = register_type ``:bounded_signed192``;

val _ = translate compute_boundedWideSignedTheory.bounded192_is_zero_def;
val _ = translate compute_boundedWideSignedTheory.bounded_signed192_make_def;
val _ = translate compute_boundedWideSignedTheory.bounded_signed192_add_def;
val _ = translate compute_boundedWideSignedTheory.bounded_signed64_scale81_def;
val _ = translate compute_boundedWideSignedTheory.bounded128_scale41_def;
val _ = translate compute_boundedWideSignedTheory.bounded192_shift_floor81_words_def;
val _ = translate compute_boundedWideSignedTheory.bounded192_low81_nonzero_def;
val _ = translate compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def;
val _ = translate compute_boundedWideSignedTheory.bounded_signed192_shift_floor81_64_def;
val _ = translate compute_boundedWideSignedTheory.bounded_signed192_shift_ceil81_64_def;

val _ = export_theory ();
