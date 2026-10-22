(*****************************************************************************
 * Signed rational conversion for source-program constants.
 *
 * Coordinate boxes in the authenticated packet are positive, but polynomial
 * constants use the full HOL Light rational encoding
 *
 *   Pair (Pair (Num positive) (Num negative)) (Num (denominator - 1)).
 *
 * The historical source rounds those constants outward at scale 10^12.
 * Keep that signed conversion separate from the positive-box decoder so the
 * latter retains its deliberately narrow fail-closed contract.
 *****************************************************************************)
Theory compute_boundedObjectSignedDecimalQ
Ancestors
  compute_boundedObjectDecimalQ
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();
val _ = monadsyntax.temp_enable_monad "option";

Definition bounded_object_q_floor64_decimal_def:
  bounded_object_q_floor64_decimal
      (Pair (Pair (Num positive) (Num negative))
        (Num denominator_minus_one) : cv) =
    (if positive < negative then
       case bounded_decimal_natural_ceil64 (negative - positive)
              (SUC denominator_minus_one) of
       | NONE => NONE
       | SOME magnitude => SOME (BoundedSigned64 T magnitude)
     else
       case bounded_decimal_natural_floor64 (positive - negative)
              (SUC denominator_minus_one) of
       | NONE => NONE
       | SOME magnitude => SOME (BoundedSigned64 F magnitude)) /\
  bounded_object_q_floor64_decimal _ = NONE
End

Definition bounded_object_q_ceil64_decimal_def:
  bounded_object_q_ceil64_decimal
      (Pair (Pair (Num positive) (Num negative))
        (Num denominator_minus_one) : cv) =
    (if positive < negative then
       case bounded_decimal_natural_floor64 (negative - positive)
              (SUC denominator_minus_one) of
       | NONE => NONE
       | SOME magnitude => SOME (BoundedSigned64 T magnitude)
     else
       case bounded_decimal_natural_ceil64 (positive - negative)
              (SUC denominator_minus_one) of
       | NONE => NONE
       | SOME magnitude => SOME (BoundedSigned64 F magnitude)) /\
  bounded_object_q_ceil64_decimal _ = NONE
End

Definition bounded_object_q_constant_interval64_decimal_def:
  bounded_object_q_constant_interval64_decimal encoded =
    do
      lower <- bounded_object_q_floor64_decimal encoded;
      upper <- bounded_object_q_ceil64_decimal encoded;
      if bounded_interval64_valid (BoundedInterval64 lower upper) then
        SOME (BoundedInterval64 lower upper)
      else NONE
    od
End

Theorem bounded_object_q_floor64_decimal_positive:
  bounded_object_q_floor64_decimal
      (Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one)) =
    bounded_object_positive_q_floor64_decimal
      (Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one))
Proof
  simp [bounded_object_q_floor64_decimal_def,
        compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def]
QED

Theorem bounded_object_q_ceil64_decimal_positive:
  bounded_object_q_ceil64_decimal
      (Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one)) =
    bounded_object_positive_q_ceil64_decimal
      (Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one))
Proof
  simp [bounded_object_q_ceil64_decimal_def,
        compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def]
QED

Theorem bounded_object_signed_q_decimal_closed_tests:
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 1) (Num 0)) (Num 2)) =
    SOME
      (BoundedInterval64
        (BoundedSigned64 F 333333333333w)
        (BoundedSigned64 F 333333333334w)) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 0) (Num 1)) (Num 2)) =
    SOME
      (BoundedInterval64
        (BoundedSigned64 T 333333333334w)
        (BoundedSigned64 T 333333333333w)) /\
  bounded_object_q_constant_interval64_decimal
      (Pair (Pair (Num 1) (Num 1)) (Num 0)) =
    SOME
      (BoundedInterval64
        (BoundedSigned64 F 0w)
        (BoundedSigned64 F 0w))
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
  >> simp (CONJUNCTS
       (DB.fetch "compute_boundedObjectDecimalQ"
          "bounded_object_positive_q_floor64_decimal_compute"))
QED

val _ = export_theory ();
