(*****************************************************************************
 * Historical Flyspeck delta value at decimal fixed scale 10^12.
 *
 * The scale-independent signed-192 cubic accumulation is reused unchanged.
 * Only the final outward normalization changes: three scale-10^12 factors
 * produce a scale-10^36 raw sum, so returning to scale 10^12 divides once by
 * 10^24.
 *****************************************************************************)
Theory compute_boundedHistoricalDeltaDecimal
Ancestors
  compute_boundedHistoricalDelta compute_boundedTaylorCompleteDecimal
  compute_boundedObjectDecimalQ
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();

Definition bounded192_floor64_decimal_squared_def:
  bounded192_floor64_decimal_squared magnitude =
    let quotient =
      bounded192_to_num magnitude DIV 1000000000000000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded192_ceil64_decimal_squared_def:
  bounded192_ceil64_decimal_squared magnitude =
    let quotient =
      (bounded192_to_num magnitude + 999999999999999999999999) DIV
        1000000000000000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded_signed192_floor64_decimal_squared_def:
  bounded_signed192_floor64_decimal_squared
      (BoundedSigned192 negative magnitude) =
    case (if negative then bounded192_ceil64_decimal_squared magnitude
          else bounded192_floor64_decimal_squared magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_signed192_ceil64_decimal_squared_def:
  bounded_signed192_ceil64_decimal_squared
      (BoundedSigned192 negative magnitude) =
    case (if negative then bounded192_floor64_decimal_squared magnitude
          else bounded192_ceil64_decimal_squared magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_historical_raw_round_decimal_def:
  bounded_historical_raw_round_decimal (lower,upper) =
    case bounded_signed192_floor64_decimal_squared lower of
    | NONE => NONE
    | SOME rounded_lower =>
      case bounded_signed192_ceil64_decimal_squared upper of
      | NONE => NONE
      | SOME rounded_upper =>
          SOME (BoundedInterval64 rounded_lower rounded_upper)
End

Definition bounded_historical_delta64_value_six_decimal_def:
  bounded_historical_delta64_value_six_decimal x0 x1 x2 x3 x4 x5 =
    case bounded_interval64_sum
      [bounded_interval64_neg x0;x1;x2;
       bounded_interval64_neg x3;x4;x5] of
    | NONE => NONE
    | SOME first_linear =>
      case bounded_interval64_sum
        [x0;bounded_interval64_neg x1;x2;x3;
         bounded_interval64_neg x4;x5] of
      | NONE => NONE
      | SOME second_linear =>
        case bounded_interval64_sum
          [x0;x1;bounded_interval64_neg x2;x3;x4;
           bounded_interval64_neg x5] of
        | NONE => NONE
        | SOME third_linear =>
          case bounded_historical_raw_cubics
            [(x0,x3,first_linear,F);
             (x1,x4,second_linear,F);
             (x2,x5,third_linear,F);
             (x1,x2,x3,T);
             (x0,x2,x4,T);
             (x0,x1,x5,T);
             (x3,x4,x5,T)] of
          | NONE => NONE
          | SOME raw_terms =>
            case bounded_signed192_interval_sum raw_terms of
            | NONE => NONE
            | SOME raw => bounded_historical_raw_round_decimal raw
End

Definition bounded_historical_delta64_value_decimal_def:
  bounded_historical_delta64_value_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
        bounded_historical_delta64_value_six_decimal x0 x1 x2 x3 x4 x5
    | _ => NONE
End

Theorem bounded192_floor64_decimal_squared_value:
  bounded192_floor64_decimal_squared magnitude = SOME result ==>
  w2n result =
    bounded192_to_num magnitude DIV 1000000000000000000000000
Proof
  rw [bounded192_floor64_decimal_squared_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def,
          wordsTheory.w2n_n2w]
QED

Theorem bounded192_ceil64_decimal_squared_value:
  bounded192_ceil64_decimal_squared magnitude = SOME result ==>
  w2n result =
    (bounded192_to_num magnitude + 999999999999999999999999) DIV
      1000000000000000000000000
Proof
  rw [bounded192_ceil64_decimal_squared_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def,
          wordsTheory.w2n_n2w]
QED

Theorem bounded_signed192_floor64_decimal_squared_lower_bound:
  bounded_signed192_floor64_decimal_squared source = SOME result ==>
  (&1000000000000000000000000:int) *
      bounded_signed64_to_int result <=
    bounded_signed192_to_int source
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> rw [bounded_signed192_floor64_decimal_squared_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded192_floor64_decimal_squared_value
  >> imp_res_tac bounded192_ceil64_decimal_squared_value
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_floor_scaled_le)
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_ceil_scaled_ge)
  >> fs [compute_boundedWideSignedTheory.bounded_signed192_to_int_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_make_value]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed192_ceil64_decimal_squared_upper_bound:
  bounded_signed192_ceil64_decimal_squared source = SOME result ==>
  bounded_signed192_to_int source <=
    (&1000000000000000000000000:int) *
      bounded_signed64_to_int result
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> rw [bounded_signed192_ceil64_decimal_squared_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded192_floor64_decimal_squared_value
  >> imp_res_tac bounded192_ceil64_decimal_squared_value
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_floor_scaled_le)
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_ceil_scaled_ge)
  >> fs [compute_boundedWideSignedTheory.bounded_signed192_to_int_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_make_value]
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_raw_round_decimal_contains_int:
  bounded_signed192_interval_contains_int raw exact_value /\
  bounded_historical_raw_round_decimal raw = SOME result ==>
  bounded_interval64_contains_scaled_int result
    (&1000000000000000000000000:int) exact_value
Proof
  Cases_on `raw`
  >> Cases_on `result`
  >> rw [bounded_historical_raw_round_decimal_def,
         compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_contains_int_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_signed192_floor64_decimal_squared_lower_bound
  >> imp_res_tac
       bounded_signed192_ceil64_decimal_squared_upper_bound
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_delta64_value_six_decimal_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 /\
  bounded_interval64_contains_int x1 v1 /\
  bounded_interval64_contains_int x2 v2 /\
  bounded_interval64_contains_int x3 v3 /\
  bounded_interval64_contains_int x4 v4 /\
  bounded_interval64_contains_int x5 v5 /\
  bounded_historical_delta64_value_six_decimal x0 x1 x2 x3 x4 x5 =
    SOME result ==>
  bounded_interval64_contains_scaled_int result
    (&1000000000000000000000000:int)
    (bounded_delta_value v0 v1 v2 v3 v4 v5)
Proof
  rw [bounded_historical_delta64_value_six_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_neg_contains_int
  >> imp_res_tac
       compute_boundedDeltaTaylorTheory.bounded_interval64_sum6_contains_int_from_result
  >> `LIST_REL bounded_historical_raw_cubic_input_represents
       [(x0,x3,x'',F);(x1,x4,x',F);(x2,x5,x,F);
        (x1,x2,x3,T);(x0,x2,x4,T);(x0,x1,x5,T);(x3,x4,x5,T)]
       [(v0 * v3) * (-v0 + v1 + v2 + -v3 + v4 + v5);
        (v1 * v4) * (v0 + -v1 + v2 + v3 + -v4 + v5);
        (v2 * v5) * (v0 + v1 + -v2 + v3 + v4 + -v5);
        -((v1 * v2) * v3);-((v0 * v2) * v4);
        -((v0 * v1) * v5);-((v3 * v4) * v5)]` by
       (simp [LIST_REL_def]
        >> metis_tac
             [compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_input_represents_def])
  >> imp_res_tac
       compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_contains_ints
  >> imp_res_tac
       compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_contains_int
  >> imp_res_tac bounded_historical_raw_round_decimal_contains_int
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta_value_sum_of_products]
QED

Theorem bounded_historical_delta64_value_decimal_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 /\
  bounded_interval64_contains_int x1 v1 /\
  bounded_interval64_contains_int x2 v2 /\
  bounded_interval64_contains_int x3 v3 /\
  bounded_interval64_contains_int x4 v4 /\
  bounded_interval64_contains_int x5 v5 /\
  bounded_historical_delta64_value_decimal [x0;x1;x2;x3;x4;x5] =
    SOME result ==>
  bounded_interval64_contains_scaled_int result
    (&1000000000000000000000000:int)
    (bounded_delta_value v0 v1 v2 v3 v4 v5)
Proof
  simp [bounded_historical_delta64_value_decimal_def]
  >> metis_tac
       [bounded_historical_delta64_value_six_decimal_contains_scaled_int]
QED

Theorem bounded_historical_delta64_decimal_closed_tests:
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 2000000000000w) in
  bounded_historical_delta64_value_decimal (REPLICATE 6 one) = SOME two /\
  bounded_historical_delta64_value_decimal [] = NONE /\
  bounded_historical_delta64_value_decimal [one] = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
