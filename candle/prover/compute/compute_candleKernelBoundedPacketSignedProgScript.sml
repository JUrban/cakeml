(* Kernel-lineage checkpoint for signed bounded endpoint arithmetic. *)
Theory compute_candleKernelBoundedPacketSignedProg
Ancestors
  compute_candleKernelBoundedPacketBaseProg
  compute_boundedSigned compute_boundedSignedAdd
  compute_boundedSignedEndpoint compute_boundedSignedEndpointAdd
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends
  "compute_candleKernelBoundedPacketBaseProg";

val _ = register_type ``:bounded_signed64``;
val _ = register_type ``:bounded_signed128``;

val _ = translate compute_boundedSignedTheory.bounded128_is_zero_def;
val _ = translate compute_boundedSignedTheory.bounded_signed128_make_def;
val _ = translate compute_boundedSignedTheory.bounded_signed128_negative_def;
val _ = translate compute_boundedSignedTheory.bounded_signed128_magnitude_def;
val _ = translate compute_boundedSignedTheory.bounded_word64_low40_nonzero_def;
val _ = translate compute_boundedSignedTheory.bounded_word64_mul_shift_ceil40_def;
val _ = translate compute_boundedSignedTheory.bounded_signed_word64_mul_floor40_def;
val _ = translate compute_boundedSignedTheory.bounded_signed_word64_mul_ceil40_def;

val _ = translate compute_boundedSignedAddTheory.bounded128_le_words_def;
val _ = translate compute_boundedSignedAddTheory.bounded_word64_sub_borrow_def;
val _ = translate compute_boundedSignedAddTheory.bounded128_sub_words_def;
val _ = translate compute_boundedSignedAddTheory.bounded_signed128_add_def;

val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_make_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_widen128_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_le_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_min_def;
val _ = translate compute_boundedSignedEndpointTheory.bounded_signed64_max_def;

val _ = translate compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def;
val _ = translate compute_boundedSignedEndpointAddTheory.bounded_signed64_add_def;

val _ = export_theory ();
