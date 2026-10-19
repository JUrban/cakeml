(*****************************************************************************
 * Successful positive-rational decimal conversion fixes the source cval to
 * the canonical positive rational representation.
 *****************************************************************************)
Theory compute_boundedPositiveQShape
Ancestors
  compute_boundedObjectDecimalQ
Libs
  bossLib preamble

Theorem bounded_object_positive_q_floor64_decimal_shape:
  bounded_object_positive_q_floor64_decimal encoded = SOME result ==>
  ?value denominator_minus_one.
    encoded =
      Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one)
Proof
  Cases_on `encoded`
  >> fs [bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c`
  >> fs [bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c'`
  >> fs [bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c0'`
  >> fs [bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `n'`
  >> fs [bounded_object_positive_q_floor64_decimal_def]
  >> Cases_on `c0`
  >> fs [bounded_object_positive_q_floor64_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_positive_q_ceil64_decimal_shape:
  bounded_object_positive_q_ceil64_decimal encoded = SOME result ==>
  ?value denominator_minus_one.
    encoded =
      Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one)
Proof
  Cases_on `encoded`
  >> fs [bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c`
  >> fs [bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c'`
  >> fs [bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c0'`
  >> fs [bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `n'`
  >> fs [bounded_object_positive_q_ceil64_decimal_def]
  >> Cases_on `c0`
  >> fs [bounded_object_positive_q_ceil64_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_positive_q_interval64_decimal_shape:
  bounded_object_positive_q_interval64_decimal encoded = SOME result ==>
  ?lower_value lower_denominator_minus_one
   upper_value upper_denominator_minus_one.
    encoded =
      Pair
        (Pair (Pair (Num lower_value) (Num 0))
          (Num lower_denominator_minus_one))
        (Pair (Pair (Num upper_value) (Num 0))
          (Num upper_denominator_minus_one))
Proof
  Cases_on `encoded`
  >> rw [bounded_object_positive_q_interval64_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_positive_q_floor64_decimal_shape
  >> imp_res_tac bounded_object_positive_q_ceil64_decimal_shape
  >> gvs []
QED

val _ = export_theory ();
