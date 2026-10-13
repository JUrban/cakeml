(* Kernel-lineage checkpoint for the complete Taylor verdict and certificates. *)
Theory compute_candleKernelBoundedPacketTaylorProg
Ancestors
  compute_candleKernelBoundedPacketIntervalProg
  compute_boundedTaylorComplete compute_boundedTaylorGradient
  compute_boundedSqrtCertificate compute_boundedReciprocalCertificate
  compute_boundedAtan
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib

val _ = m_translation_extends
  "compute_candleKernelBoundedPacketIntervalProg";

val _ = translate compute_boundedTaylorCompleteTheory.bounded_interval64_abs_upper_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_word64_product128_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_taylor_error_def;
val _ = translate compute_boundedTaylorCompleteTheory.bounded_taylor_value_complete_def;

val _ = translate compute_boundedTaylorGradientTheory.bounded_signed64_scale40_128_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded128_low40_nonzero_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_signed128_shift_floor40_64_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_signed128_shift_ceil40_64_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_taylor_gradient_row_complete_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_taylor_gradient_rows_complete_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_taylor_gradient_complete_def;
val _ = translate compute_boundedTaylorGradientTheory.bounded_taylor64_complete_def;

val _ = translate compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_def;

val _ = translate compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def;
val _ = translate compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def;
val _ = translate compute_boundedReciprocalCertificateTheory.bounded_scale_squared128_def;
val _ = translate compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def;

val _ = translate compute_boundedAtanTheory.bounded_atan_word64_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_scale_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_one_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_pi_half_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_pos_third_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_neg_third_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_pos_fifth_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_neg_seventh_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_pos_ninth_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_neg_eleventh_def;
val _ = translate compute_boundedAtanTheory.bounded_atan_pos_thirteenth_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_mul_add_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_pos_lower_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_pos_upper_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_unit_lower_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_unit_upper_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_unit_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_range_point_def;
val _ = translate compute_boundedAtanTheory.bounded_interval64_atan_range_def;

val _ = export_theory ();
