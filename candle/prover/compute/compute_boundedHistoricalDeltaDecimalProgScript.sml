(* CakeML translation of the historical delta block at decimal scale. *)
Theory compute_boundedHistoricalDeltaDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorAtanDecimalProg compute_boundedHistoricalDeltaDecimal

val _ = translation_extends "compute_boundedTaylorAtanDecimalProg";

val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_source_interval64_sum_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_six_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def;

(* Install the scale-independent cubic accumulator on the decimal program
 * chain.  Only the normalization and public delta entry points below are new
 * scale-specific operations. *)
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def;
val _ = translate
  compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed192_le_words_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed192_min_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed192_max_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed192_neg_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed128_nonnegative_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed128_nonpositive_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed128_mul_signed64_raw192_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_from_pairs_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_mixed_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_mul64_unchecked_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_signed_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def;
val _ = translate
  compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_def;

val _ = translate
  (compute_boundedHistoricalDeltaDecimalTheory.bounded192_floor64_decimal_squared_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedHistoricalDeltaDecimalTheory.bounded192_ceil64_decimal_squared_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_signed192_floor64_decimal_squared_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_signed192_ceil64_decimal_squared_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_raw_round_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_six_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def;

val _ = export_theory ();
