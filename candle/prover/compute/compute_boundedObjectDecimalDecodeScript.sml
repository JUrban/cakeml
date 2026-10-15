(*****************************************************************************
 * Exact object-to-word boundary for the decimal fast nonlinear checker.
 *
 * Candle's object checker represents a signed integer as (positive,negative).
 * The fast carrier uses one sign bit and a word64 magnitude.  This decoder is
 * intentionally fail-closed: it accepts only canonical one-sided object
 * values that fit in one word, and only ordered normalized intervals.
 *****************************************************************************)
Theory compute_boundedObjectDecimalDecode
Ancestors
  compute_boundedCertificateDecimal compute_boundedObjectIntervalRelation
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();
val _ = monadsyntax.temp_enable_monad "option";

Definition bounded_object_decimal_signed64_def:
  bounded_object_decimal_signed64
      (Pair (Num positive) (Num negative) : cv) =
    (if negative = 0 then
       if positive < bounded_word_base then
         SOME (BoundedSigned64 F ((n2w positive):word64))
       else NONE
     else if positive = 0 /\ negative < bounded_word_base then
       SOME (BoundedSigned64 T ((n2w negative):word64))
     else NONE) /\
  bounded_object_decimal_signed64 _ = NONE
End

Definition bounded_object_decimal_interval64_def:
  bounded_object_decimal_interval64 (Pair lower upper : cv) =
    do
      lower' <- bounded_object_decimal_signed64 lower;
      upper' <- bounded_object_decimal_signed64 upper;
      if bounded_interval64_valid (BoundedInterval64 lower' upper') then
        SOME (BoundedInterval64 lower' upper')
      else NONE
    od /\
  bounded_object_decimal_interval64 _ = NONE
End

Definition bounded_object_decimal_interval64_list_def:
  bounded_object_decimal_interval64_list (Num 0 : cv) = SOME [] /\
  bounded_object_decimal_interval64_list (Pair interval intervals) =
    do
      interval' <- bounded_object_decimal_interval64 interval;
      intervals' <- bounded_object_decimal_interval64_list intervals;
      return (interval'::intervals')
    od /\
  bounded_object_decimal_interval64_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_interval64_object_cv_list_def:
  bounded_interval64_object_cv_list [] = (Num 0 : cv) /\
  bounded_interval64_object_cv_list (interval::intervals) =
    Pair (bounded_interval64_object_cv interval)
      (bounded_interval64_object_cv_list intervals)
End

Theorem bounded_object_decimal_signed64_exact:
  bounded_object_decimal_signed64 encoded = SOME value ==>
  bounded_signed64_normalized value /\
  bounded_object_signed_int encoded =
    SOME (bounded_signed64_to_int value) /\
  bounded_signed64_object_cv value = encoded
Proof
  Cases_on `encoded`
  >> fs [bounded_object_decimal_signed64_def]
  >> Cases_on `c`
  >> fs [bounded_object_decimal_signed64_def]
  >> Cases_on `c0`
  >> fs [bounded_object_decimal_signed64_def]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def]
  >> strip_tac
  >> gvs [
          compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
          compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
          compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
          compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
          wordsTheory.w2n_n2w, wordsTheory.dimword_64]
QED

Theorem bounded_object_decimal_signed64_object_cv[simp]:
  bounded_signed64_normalized value ==>
  bounded_object_decimal_signed64
    (bounded_signed64_object_cv value) = SOME value
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> simp [bounded_object_decimal_signed64_def,
           compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
           compute_boundedTheory.bounded_word_base_def,
           wordsTheory.n2w_w2n]
  >> qspec_then `c` mp_tac wordsTheory.w2n_lt
  >> simp [wordsTheory.dimword_64]
QED

Theorem bounded_object_decimal_signed64_rejects_noncanonical:
  0 < positive /\ 0 < negative ==>
  bounded_object_decimal_signed64
    (Pair (Num positive) (Num negative)) = NONE
Proof
  simp [bounded_object_decimal_signed64_def]
QED

Theorem bounded_object_decimal_signed64_rejects_overflow:
  bounded_word_base <= positive ==>
  bounded_object_decimal_signed64
    (Pair (Num positive) (Num 0)) = NONE
Proof
  simp [bounded_object_decimal_signed64_def]
QED

Theorem bounded_object_decimal_interval64_exact:
  bounded_object_decimal_interval64 encoded = SOME interval ==>
  bounded_interval64_valid interval /\
  bounded_object_interval_ints encoded =
    SOME
      (bounded_signed64_to_int (bounded_interval64_lower interval),
       bounded_signed64_to_int (bounded_interval64_upper interval)) /\
  bounded_interval64_object_cv interval = encoded
Proof
  Cases_on `encoded`
  >> fs [bounded_object_decimal_interval64_def]
  >> strip_tac
  >> imp_res_tac bounded_object_decimal_signed64_exact
  >> gvs [compute_boundedObjectIntervalRelationTheory.bounded_object_interval_ints_def,
          compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
          compute_boundedIntervalTheory.bounded_interval64_lower_def,
          compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_object_decimal_interval64_object_cv[simp]:
  bounded_interval64_valid interval ==>
  bounded_object_decimal_interval64
    (bounded_interval64_object_cv interval) = SOME interval
Proof
  Cases_on `interval`
  >> simp [bounded_object_decimal_interval64_def,
           compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
           compute_boundedIntervalTheory.bounded_interval64_valid_def]
QED

Theorem bounded_object_decimal_interval64_list_exact:
  !encoded intervals.
    bounded_object_decimal_interval64_list encoded = SOME intervals ==>
    EVERY bounded_interval64_valid intervals /\
    bounded_interval64_object_cv_list intervals = encoded
Proof
  ho_match_mp_tac bounded_object_decimal_interval64_list_ind
  >> rw [bounded_object_decimal_interval64_list_def]
  >> every_case_tac
  >> gvs [bounded_interval64_object_cv_list_def]
  >> imp_res_tac bounded_object_decimal_interval64_exact
  >> metis_tac []
QED

Theorem bounded_object_decimal_interval64_list_roundtrip[simp]:
  EVERY bounded_interval64_valid intervals ==>
  bounded_object_decimal_interval64_list
    (bounded_interval64_object_cv_list intervals) = SOME intervals
Proof
  Induct_on `intervals`
  >> simp [bounded_interval64_object_cv_list_def,
           bounded_object_decimal_interval64_list_def]
QED

Theorem bounded_object_decimal_decode_closed_tests:
  bounded_object_decimal_signed64
      (Pair (Num 7) (Num 0)) = SOME (BoundedSigned64 F 7w) /\
  bounded_object_decimal_signed64
      (Pair (Num 0) (Num 7)) = SOME (BoundedSigned64 T 7w) /\
  bounded_object_decimal_signed64
      (Pair (Num 0) (Num 0)) = SOME (BoundedSigned64 F 0w) /\
  bounded_object_decimal_signed64
      (Pair (Num 7) (Num 3)) = NONE /\
  bounded_object_decimal_interval64
      (Pair (Pair (Num 2) (Num 0)) (Pair (Num 3) (Num 0))) =
    SOME
      (BoundedInterval64
        (BoundedSigned64 F 2w) (BoundedSigned64 F 3w)) /\
  bounded_object_decimal_interval64
      (Pair (Pair (Num 3) (Num 0)) (Pair (Num 2) (Num 0))) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
