(* CakeML translation of decimal compact-Taylor completion. *)
Theory compute_boundedTaylorCompleteDecimalProg
Libs
  preamble ml_translatorLib ml_progLib
Ancestors
  compute_boundedTaylorProductDecimalProg compute_boundedTaylorGradientProg
  compute_boundedTaylorCompleteDecimal

val _ = translation_extends "compute_boundedTaylorProductDecimalProg";

val bounded128_to_num_v =
  translate
    (compute_boundedTheory.bounded128_to_num_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);

val bounded128_floor64_decimal_v =
  translate
    (compute_boundedTaylorCompleteDecimalTheory.bounded128_floor64_decimal_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val bounded128_ceil64_decimal_v =
  translate
    (compute_boundedTaylorCompleteDecimalTheory.bounded128_ceil64_decimal_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val bounded_signed128_floor64_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_signed128_floor64_decimal_def;
val bounded_signed128_ceil64_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_signed128_ceil64_decimal_def;
val bounded_signed64_scale_decimal128_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_signed64_scale_decimal128_def;
val bounded_taylor_gradient_row_complete_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_row_complete_decimal_def;
val bounded_taylor_gradient_rows_complete_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_rows_complete_decimal_def;
val bounded_taylor_gradient_complete_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_complete_decimal_def;
val bounded_taylor_error_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_error_decimal_def;
val bounded_signed64_scale_two_decimal_squared192_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_signed64_scale_two_decimal_squared192_def;
val bounded192_floor64_two_decimal_squared_v =
  translate
    (compute_boundedTaylorCompleteDecimalTheory.bounded192_floor64_two_decimal_squared_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val bounded192_ceil64_two_decimal_squared_v =
  translate
    (compute_boundedTaylorCompleteDecimalTheory.bounded192_ceil64_two_decimal_squared_def
     |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val bounded_signed192_floor64_two_decimal_squared_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_signed192_floor64_two_decimal_squared_def;
val bounded_signed192_ceil64_two_decimal_squared_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_signed192_ceil64_two_decimal_squared_def;
val bounded_taylor_value_complete_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_value_complete_decimal_def;
val bounded_taylor64_complete_decimal_v =
  translate
    compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_def;

val _ = export_theory ();
