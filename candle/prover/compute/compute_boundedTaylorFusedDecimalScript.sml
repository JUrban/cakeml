(*****************************************************************************
 * Decimal fixed-scale rounding for fused Taylor product sums.
 *
 * The authenticated HOL Light checker accumulates raw products before one
 * outward normalization at scale 10^12.  Reusing the dyadic shift-40
 * boundary, or rounding each product separately, would not refine that
 * operation.  This theory keeps the existing checked signed-192 accumulator
 * and changes only its final directed normalization.
 *****************************************************************************)
Theory compute_boundedTaylorFusedDecimal
Ancestors
  compute_boundedObjectDecimalQ compute_boundedTaylorMul
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();

Definition bounded192_floor64_decimal_def:
  bounded192_floor64_decimal magnitude =
    let quotient = bounded192_to_num magnitude DIV 1000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded192_ceil64_decimal_def:
  bounded192_ceil64_decimal magnitude =
    let quotient =
      (bounded192_to_num magnitude + 999999999999) DIV 1000000000000 in
    if quotient < bounded_word_base then
      SOME ((n2w quotient):word64)
    else NONE
End

Definition bounded_signed192_floor64_decimal_def:
  bounded_signed192_floor64_decimal
      (BoundedSigned192 negative magnitude) =
    case (if negative then bounded192_ceil64_decimal magnitude
          else bounded192_floor64_decimal magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_signed192_ceil64_decimal_def:
  bounded_signed192_ceil64_decimal
      (BoundedSigned192 negative magnitude) =
    case (if negative then bounded192_floor64_decimal magnitude
          else bounded192_ceil64_decimal magnitude) of
    | NONE => NONE
    | SOME quotient => SOME (bounded_signed64_make negative quotient)
End

Definition bounded_interval64_fused_products_decimal_def:
  bounded_interval64_fused_products_decimal products =
    let zero = bounded_signed192_make F bounded192_zero in
    case bounded_interval64_raw_sum_acc products zero zero of
    | NONE => NONE
    | SOME (raw_lower,raw_upper) =>
      case bounded_signed192_floor64_decimal raw_lower of
      | NONE => NONE
      | SOME lower =>
        case bounded_signed192_ceil64_decimal raw_upper of
        | NONE => NONE
        | SOME upper => SOME (BoundedInterval64 lower upper)
End

Theorem bounded192_floor64_decimal_value:
  bounded192_floor64_decimal magnitude = SOME result ==>
  w2n result = bounded192_to_num magnitude DIV 1000000000000
Proof
  rw [bounded192_floor64_decimal_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def,
          wordsTheory.w2n_n2w]
QED

Theorem bounded192_ceil64_decimal_value:
  bounded192_ceil64_decimal magnitude = SOME result ==>
  w2n result =
    (bounded192_to_num magnitude + 999999999999) DIV 1000000000000
Proof
  rw [bounded192_ceil64_decimal_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def,
          wordsTheory.w2n_n2w]
QED

Theorem bounded_signed192_floor64_decimal_normalized:
  bounded_signed192_floor64_decimal source = SOME result ==>
  bounded_signed64_normalized result
Proof
  Cases_on `source`
  >> rw [bounded_signed192_floor64_decimal_def]
  >> every_case_tac
  >> gvs [compute_boundedSignedEndpointTheory.bounded_signed64_make_normalized]
QED

Theorem bounded_signed192_ceil64_decimal_normalized:
  bounded_signed192_ceil64_decimal source = SOME result ==>
  bounded_signed64_normalized result
Proof
  Cases_on `source`
  >> rw [bounded_signed192_ceil64_decimal_def]
  >> every_case_tac
  >> gvs [compute_boundedSignedEndpointTheory.bounded_signed64_make_normalized]
QED

Theorem bounded_signed192_floor64_decimal_lower_bound:
  bounded_signed192_floor64_decimal source = SOME result ==>
  (&1000000000000:int) * bounded_signed64_to_int result <=
    bounded_signed192_to_int source
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> rw [bounded_signed192_floor64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded192_floor64_decimal_value
  >> imp_res_tac bounded192_ceil64_decimal_value
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_floor_scaled_le)
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_ceil_scaled_ge)
  >> fs [compute_boundedWideSignedTheory.bounded_signed192_to_int_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_make_value]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed192_ceil64_decimal_upper_bound:
  bounded_signed192_ceil64_decimal source = SOME result ==>
  bounded_signed192_to_int source <=
    (&1000000000000:int) * bounded_signed64_to_int result
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> rw [bounded_signed192_ceil64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded192_floor64_decimal_value
  >> imp_res_tac bounded192_ceil64_decimal_value
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_floor_scaled_le)
  >> assume_tac
       (Q.INST
          [`value` |-> `bounded192_to_num magnitude`,
           `denominator` |-> `1000000000000`]
          compute_boundedObjectDecimalQTheory.bounded_natural_div_ceil_scaled_ge)
  >> fs [compute_boundedWideSignedTheory.bounded_signed192_to_int_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_make_value]
  >> intLib.ARITH_TAC
QED

Theorem bounded_fused_raw_round_decimal_contains_int:
  bounded_fused_raw_interval_contains_int
      (raw_lower,raw_upper) exact_value /\
  bounded_signed192_floor64_decimal raw_lower = SOME lower /\
  bounded_signed192_ceil64_decimal raw_upper = SOME upper ==>
  bounded_interval64_contains_scaled_int
    (BoundedInterval64 lower upper) (&1000000000000:int) exact_value
Proof
  rw [compute_boundedTaylorMulTheory.bounded_fused_raw_interval_contains_int_def,
      compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def]
  >> imp_res_tac bounded_signed192_floor64_decimal_lower_bound
  >> imp_res_tac bounded_signed192_ceil64_decimal_upper_bound
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_fused_products_decimal_contains_scaled_int:
  LIST_REL bounded_fused_product_input_represents products exact_values /\
  bounded_interval64_fused_products_decimal products = SOME result ==>
  bounded_interval64_contains_scaled_int result (&1000000000000:int)
    (FOLDL (λtotal value:int. total + value) 0 exact_values)
Proof
  rw [bounded_interval64_fused_products_decimal_def, LET_THM]
  >> every_case_tac
  >> gvs []
  >> `bounded_fused_raw_interval_contains_int
        (bounded_signed192_make F bounded192_zero,
         bounded_signed192_make F bounded192_zero) 0` by
       simp [compute_boundedTaylorMulTheory.bounded_fused_raw_interval_contains_int_def,
             compute_boundedWideSignedTheory.bounded_signed192_make_value,
             compute_boundedWideTheory.bounded192_zero_def,
             compute_boundedTheory.bounded192_to_num_def]
  >> imp_res_tac
       compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_contains_int
  >> imp_res_tac bounded_fused_raw_round_decimal_contains_int
QED

Theorem bounded_taylor_fused_decimal_closed_tests:
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  let tiny = BoundedInterval64
    (BoundedSigned64 F 1w) (BoundedSigned64 F 1w) in
  let negative_tiny = BoundedInterval64
    (BoundedSigned64 T 1w) (BoundedSigned64 T 1w) in
  bounded_interval64_fused_products_decimal [(one,one)] = SOME one /\
  bounded_interval64_fused_products_decimal [(tiny,tiny);(tiny,tiny)] =
    SOME (BoundedInterval64
      (BoundedSigned64 F 0w) (BoundedSigned64 F 1w)) /\
  bounded_interval64_fused_products_decimal [(negative_tiny,tiny)] =
    SOME (BoundedInterval64
      (BoundedSigned64 T 1w) (BoundedSigned64 F 0w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
