(*****************************************************************************
 * Reusable cv_compute translations for the fixed-word runtime-certificate
 * trace.  The numerical checker remains the existing word checker; these
 * translations only select and accumulate the exact interval packet that the
 * object dispatcher consumes at each certified instruction.
 *****************************************************************************)
Theory compute_boundedAnalyticRuntimeCertificateTraceCV
Ancestors
  compute_boundedAnalyticRuntimeCertificateTrace
Libs
  bossLib preamble cv_transLib

(* The word checker binds the full product and then projects its two words.
 * Present the same definition as a pair pattern so cv_auto_trans can discover
 * the already proved pair representation without changing the checker. *)
Theorem bounded_word64_mul_shift_floor40_cv_eq[local]:
  bounded_word64_mul_shift_floor40 left right =
    case bounded_word64_mul_full_chunks22 left right of
    | (high,low) => Bounded128 (high >>> 40) ((low >>> 40) + (high << 24))
Proof
  rw [compute_boundedTheory.bounded_word64_mul_shift_floor40_def]
  >> Cases_on `bounded_word64_mul_full_chunks22 left right`
  >> simp []
QED

val _ = cv_auto_trans bounded_word64_mul_shift_floor40_cv_eq;

(* Reuse the proved arithmetic implementation at the CV boundary.  This
 * avoids exposing the word-carry helper's local pair projections while the
 * equality theorem keeps the production word-level result unchanged. *)
val _ = cv_auto_trans compute_boundedTheory.bounded128_add_words_refines;

Theorem bounded_word64_mul_shift_ceil40_cv_eq[local]:
  bounded_word64_mul_shift_ceil40 left right =
    case bounded_word64_mul_full_chunks22 left right of
    | (high,low) =>
        if bounded_word64_low40_nonzero low then
          bounded128_add_words
            (bounded_word64_mul_shift_floor40 left right)
            (Bounded128 0w 1w)
        else SOME (bounded_word64_mul_shift_floor40 left right)
Proof
  Cases_on `bounded_word64_mul_full_chunks22 left right`
  >> rw [compute_boundedSignedTheory.bounded_word64_mul_shift_ceil40_def]
QED

val _ = cv_auto_trans bounded_word64_mul_shift_ceil40_cv_eq;

Theorem bounded128_sub_words_cv_eq[local]:
  bounded128_sub_words
      (Bounded128 left_high left_low)
      (Bounded128 right_high right_low) =
    if bounded128_le_words
         (Bounded128 right_high right_low)
         (Bounded128 left_high left_low)
    then
      case bounded_word64_sub_borrow left_low right_low of
      | (low_result,borrow) =>
          let borrowed_high =
            if borrow then right_high + 1w else right_high in
          SOME (Bounded128 (left_high - borrowed_high) low_result)
    else NONE
Proof
  Cases_on `bounded_word64_sub_borrow left_low right_low`
  >> rw [compute_boundedSignedAddTheory.bounded128_sub_words_def]
QED

val _ = cv_auto_trans bounded128_sub_words_cv_eq;

Theorem bounded_word64_product128_cv_eq[local]:
  bounded_word64_product128 left right =
    case bounded_word64_mul_full_chunks22 left right of
    | (high,low) => Bounded128 high low
Proof
  Cases_on `bounded_word64_mul_full_chunks22 left right`
  >> rw [compute_boundedTaylorCompleteTheory.bounded_word64_product128_def]
QED

val _ = cv_auto_trans bounded_word64_product128_cv_eq;
val _ = cv_auto_trans
  compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def;

val _ = export_theory ();
