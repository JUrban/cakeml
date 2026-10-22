(* CakeML translation of the genuine prefix-128 historical delta gate. *)
Theory compute_boundedHistoricalDeltaPackedCheckProg
Libs
  preamble ml_translatorLib ml_progLib basis
Ancestors
  compute_boundedPackedSequentialCase16594CheckProg
  compute_boundedHistoricalDeltaPackedCheck

val _ = translation_extends "compute_boundedPackedSequentialCase16594CheckProg";

val bounded_packed_chars_interval64_historical_v =
  translate
    compute_boundedPackedSequentialInputTheory.bounded_packed_chars_interval64_def;

(* The packed checker program state already contains the shared bounded-word
   and sequential-input substrate.  Install only the new historical block. *)
val bounded_signed192_le_words_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_le_words_def;
val bounded_signed192_min_historical_v =
  translate compute_boundedHistoricalDeltaTheory.bounded_signed192_min_def;
val bounded_signed192_max_historical_v =
  translate compute_boundedHistoricalDeltaTheory.bounded_signed192_max_def;
val bounded_signed192_neg_historical_v =
  translate compute_boundedHistoricalDeltaTheory.bounded_signed192_neg_def;
val bounded_signed128_nonnegative_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed128_nonnegative_def;
val bounded_signed128_nonpositive_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed128_nonpositive_def;
val bounded_signed128_mul_signed64_raw192_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed128_mul_signed64_raw192_def;
val bounded_raw128_interval_product_from_pairs_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_from_pairs_def;
val bounded_raw128_interval_product_mixed_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_mixed_def;
val bounded_raw128_interval_mul64_unchecked_historical_v =
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
val bounded_signed192_interval_sum_aux_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def;
val bounded_signed192_interval_sum_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_def;
val bounded192_shift_floor80_words_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded192_shift_floor80_words_def;
val bounded192_low80_nonzero_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded192_low80_nonzero_def;
val bounded_signed192_shift_floor80_64_historical_v =
  translate
    compute_boundedHistoricalDeltaTheory.bounded_signed192_shift_floor80_64_def;
val bounded_signed192_shift_ceil80_64_historical_v =
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

val bounded_packed_chars_historical_delta_cell_v =
  translate
    compute_boundedHistoricalDeltaPackedCheckTheory.bounded_packed_chars_historical_delta_cell_def;
val bounded_packed_chars_historical_delta_header_v =
  translate
    compute_boundedHistoricalDeltaPackedCheckTheory.bounded_packed_chars_historical_delta_header_def;
val bounded_packed_chars_historical_delta_cell_ok_v =
  translate
    compute_boundedHistoricalDeltaPackedCheckTheory.bounded_packed_chars_historical_delta_cell_ok_def;
val bounded_packed_chars_historical_delta_cells_v =
  translate
    compute_boundedHistoricalDeltaPackedCheckTheory.bounded_packed_chars_historical_delta_cells_def;
val bounded_packed_chars_historical_delta_complete_check_v =
  translate
    compute_boundedHistoricalDeltaPackedCheckTheory.bounded_packed_chars_historical_delta_complete_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_historical_delta_complete_check
         (String.explode payload)
    then TextIO.print "accepted\n"
    else TextIO.print "rejected\n"
  end;
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

Definition compute_bounded_historical_delta_packed_check_prog_def:
  compute_bounded_historical_delta_packed_check_prog = ^prog
End

val _ = export_theory ();
