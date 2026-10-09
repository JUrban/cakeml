(* CakeML translation of the fixed-layout historical delta block. *)
Theory compute_boundedHistoricalDeltaProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorMulProg compute_boundedDeltaTaylorProg
  compute_boundedHistoricalDelta

val _ = translation_extends "compute_boundedDeltaTaylorProg";

val bounded_signed192_le_words_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_le_words_def;
val bounded_signed192_min_v =
  translate compute_boundedHistoricalDeltaTheory.bounded_signed192_min_def;
val bounded_signed192_max_v =
  translate compute_boundedHistoricalDeltaTheory.bounded_signed192_max_def;
val bounded_signed192_neg_v =
  translate compute_boundedHistoricalDeltaTheory.bounded_signed192_neg_def;
val bounded_signed128_nonnegative_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed128_nonnegative_def;
val bounded_signed128_nonpositive_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed128_nonpositive_def;
val bounded_signed128_mul_signed64_raw192_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed128_mul_signed64_raw192_def;
val bounded_raw128_interval_product_from_pairs_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_from_pairs_def;
val bounded_raw128_interval_product_mixed_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_mixed_def;
val bounded_raw128_interval_mul64_unchecked_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_mul64_unchecked_def;
val bounded_historical_raw_cubic_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_def;
val bounded_historical_raw_cubic_signed_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_signed_def;
val bounded_historical_raw_cubics_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def;
val bounded_signed192_interval_sum_aux_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def;
val bounded_signed192_interval_sum_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_def;
val bounded192_shift_floor80_words_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded192_shift_floor80_words_def;
val bounded192_low80_nonzero_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded192_low80_nonzero_def;
val bounded_signed192_shift_floor80_64_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_shift_floor80_64_def;
val bounded_signed192_shift_ceil80_64_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_shift_ceil80_64_def;
val bounded_historical_raw_round80_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_historical_raw_round80_def;
val bounded_historical_delta64_value_six_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_historical_delta64_value_six_def;
val bounded_historical_delta64_value_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_historical_delta64_value_def;

val _ = export_theory ();
