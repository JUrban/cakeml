(*****************************************************************************
 * Outward conversion of authenticated Flyspeck rational boxes to the
 * decimal fixed-scale carrier used by the fast nonlinear checker.
 *
 * Flyspeck coordinate boxes are positive rationals encoded as
 *   Pair (Pair (Num numerator) (Num 0)) (Num (denominator - 1)).
 * Lower endpoints are rounded down and upper endpoints up at scale 10^12.
 * The conversion is fail-closed on every other representation and on word
 * overflow.  Its soundness statement refers to the original rational data,
 * not merely to a separately generated fixed-point fixture.
 *****************************************************************************)
Theory compute_boundedObjectDecimalQ
Ancestors
  compute_boundedObjectDecimalDecode
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();
val _ = monadsyntax.temp_enable_monad "option";

Definition bounded_decimal_natural_floor64_def:
  bounded_decimal_natural_floor64 value denominator =
    let rounded = (value * 1000000000000) DIV denominator in
    if rounded < bounded_word_base then
      SOME ((n2w rounded):word64)
    else NONE
End

Definition bounded_decimal_natural_ceil64_def:
  bounded_decimal_natural_ceil64 value denominator =
    let rounded =
      (value * 1000000000000 + (denominator - 1)) DIV denominator in
    if rounded < bounded_word_base then
      SOME ((n2w rounded):word64)
    else NONE
End

Definition bounded_object_positive_q_floor64_decimal_def:
  bounded_object_positive_q_floor64_decimal
      (Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one) : cv) =
    (case bounded_decimal_natural_floor64 value
            (SUC denominator_minus_one) of
     | NONE => NONE
     | SOME magnitude => SOME (BoundedSigned64 F magnitude)) /\
  bounded_object_positive_q_floor64_decimal _ = NONE
End

Definition bounded_object_positive_q_ceil64_decimal_def:
  bounded_object_positive_q_ceil64_decimal
      (Pair (Pair (Num value) (Num 0)) (Num denominator_minus_one) : cv) =
    (case bounded_decimal_natural_ceil64 value
            (SUC denominator_minus_one) of
     | NONE => NONE
     | SOME magnitude => SOME (BoundedSigned64 F magnitude)) /\
  bounded_object_positive_q_ceil64_decimal _ = NONE
End

Definition bounded_object_positive_q_interval64_decimal_def:
  bounded_object_positive_q_interval64_decimal (Pair lower upper : cv) =
    do
      lower' <- bounded_object_positive_q_floor64_decimal lower;
      upper' <- bounded_object_positive_q_ceil64_decimal upper;
      if bounded_interval64_valid (BoundedInterval64 lower' upper') then
        SOME (BoundedInterval64 lower' upper')
      else NONE
    od /\
  bounded_object_positive_q_interval64_decimal _ = NONE
End

Definition bounded_object_positive_q_interval64_decimal_list_def:
  bounded_object_positive_q_interval64_decimal_list (Num 0 : cv) = SOME [] /\
  bounded_object_positive_q_interval64_decimal_list
      (Pair interval intervals) =
    do
      interval' <- bounded_object_positive_q_interval64_decimal interval;
      intervals' <-
        bounded_object_positive_q_interval64_decimal_list intervals;
      return (interval'::intervals')
    od /\
  bounded_object_positive_q_interval64_decimal_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_interval64_covers_object_q_ints_decimal_def:
  bounded_interval64_covers_object_q_ints_decimal interval
      ((lower_numerator,lower_denominator),
       (upper_numerator,upper_denominator)) <=>
    0 < lower_denominator /\
    0 < upper_denominator /\
    lower_numerator * upper_denominator <=
      upper_numerator * lower_denominator /\
    lower_denominator *
        bounded_signed64_to_int (bounded_interval64_lower interval) <=
      (&1000000000000:int) * lower_numerator /\
    (&1000000000000:int) * upper_numerator <=
      upper_denominator *
        bounded_signed64_to_int (bounded_interval64_upper interval)
End

Definition bounded_interval64_list_covers_object_q_decimal_def:
  bounded_interval64_list_covers_object_q_decimal intervals encoded <=>
    case bounded_object_q_interval_list encoded of
    | NONE => F
    | SOME object_intervals =>
        LIST_REL bounded_interval64_covers_object_q_ints_decimal
          intervals object_intervals
End

Theorem bounded_decimal_natural_floor64_value:
  bounded_decimal_natural_floor64 value denominator = SOME result ==>
  w2n result = (value * 1000000000000) DIV denominator
Proof
  rw [bounded_decimal_natural_floor64_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def,
          wordsTheory.w2n_n2w]
QED

Theorem bounded_decimal_natural_ceil64_value:
  bounded_decimal_natural_ceil64 value denominator = SOME result ==>
  w2n result =
    (value * 1000000000000 + (denominator - 1)) DIV denominator
Proof
  rw [bounded_decimal_natural_ceil64_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedTheory.bounded_word_base_def,
          wordsTheory.w2n_n2w]
QED

Theorem bounded_natural_div_floor_scaled_le:
  0 < denominator ==>
  (value DIV denominator) * denominator <= value
Proof
  strip_tac
  >> mp_tac (Q.SPEC `denominator` arithmeticTheory.DIVISION)
  >> simp []
  >> disch_then (qspec_then `value` strip_assume_tac)
  >> intLib.ARITH_TAC
QED

Theorem bounded_natural_div_ceil_scaled_ge:
  0 < denominator ==>
  value <= ((value + (denominator - 1)) DIV denominator) * denominator
Proof
  strip_tac
  >> `((value + (denominator - 1)) DIV denominator =
       value DIV denominator +
         if value MOD denominator = 0 then 0 else 1)` by
       metis_tac [compute_boundedSignedTheory.bounded_div_ceil]
  >> mp_tac (Q.SPEC `denominator` arithmeticTheory.DIVISION)
  >> simp []
  >> disch_then (qspec_then `value` strip_assume_tac)
  >> Cases_on `value MOD denominator = 0`
  >- fs []
  >> fs [arithmeticTheory.LEFT_ADD_DISTRIB]
  >> `value MOD denominator < denominator` by simp []
  >> metis_tac [arithmeticTheory.ADD_MONO_LESS_EQ,
                arithmeticTheory.LESS_IMP_LESS_OR_EQ,
                arithmeticTheory.ADD_COMM]
QED

Theorem bounded_object_positive_q_floor64_decimal_exact:
  bounded_object_positive_q_floor64_decimal encoded = SOME result ==>
  ?value denominator.
    bounded_object_q_ints encoded = SOME (&value,&denominator) /\
    0 < denominator /\
    bounded_signed64_normalized result /\
    (&denominator:int) * bounded_signed64_to_int result <=
      (&1000000000000:int) * &value
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
  >> strip_tac
  >> gvs []
  >> imp_res_tac bounded_decimal_natural_floor64_value
  >> qexists_tac `n`
  >> qexists_tac `SUC n'`
  >> simp [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
           compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> mp_tac
       (Q.INST
          [`denominator` |-> `SUC n'`,
           `value` |-> `1000000000000 * n`]
          bounded_natural_div_floor_scaled_le)
  >> simp []
  >> metis_tac [arithmeticTheory.MULT_COMM]
QED

Theorem bounded_object_positive_q_ceil64_decimal_exact:
  bounded_object_positive_q_ceil64_decimal encoded = SOME result ==>
  ?value denominator.
    bounded_object_q_ints encoded = SOME (&value,&denominator) /\
    0 < denominator /\
    bounded_signed64_normalized result /\
    (&1000000000000:int) * &value <=
      (&denominator:int) * bounded_signed64_to_int result
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
  >> strip_tac
  >> gvs []
  >> imp_res_tac bounded_decimal_natural_ceil64_value
  >> qexists_tac `n`
  >> qexists_tac `SUC n'`
  >> simp [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
           compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> mp_tac
       (Q.INST
          [`denominator` |-> `SUC n'`,
           `value` |-> `1000000000000 * n`]
          bounded_natural_div_ceil_scaled_ge)
  >> simp []
  >> metis_tac [arithmeticTheory.MULT_COMM]
QED

Theorem bounded_object_positive_q_interval64_decimal_exact:
  bounded_object_positive_q_interval64_decimal encoded = SOME interval /\
  bounded_object_q_interval_ints encoded = SOME object_interval /\
  (FST (FST object_interval)) * (SND (SND object_interval)) <=
    (FST (SND object_interval)) * (SND (FST object_interval)) ==>
  bounded_interval64_valid interval /\
  bounded_interval64_covers_object_q_ints_decimal interval object_interval
Proof
  Cases_on `encoded`
  >> fs [bounded_object_positive_q_interval64_decimal_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> strip_tac
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_positive_q_floor64_decimal_exact
  >> imp_res_tac bounded_object_positive_q_ceil64_decimal_exact
  >> gvs [bounded_interval64_covers_object_q_ints_decimal_def,
          compute_boundedIntervalTheory.bounded_interval64_lower_def,
          compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_object_positive_q_interval64_decimal_list_exact:
  !encoded intervals object_intervals.
    bounded_object_positive_q_interval64_decimal_list encoded =
        SOME intervals /\
    bounded_object_q_interval_list encoded = SOME object_intervals /\
    EVERY
      (\object_interval.
        (FST (FST object_interval)) * (SND (SND object_interval)) <=
        (FST (SND object_interval)) * (SND (FST object_interval)))
      object_intervals ==>
    EVERY bounded_interval64_valid intervals /\
    LIST_REL bounded_interval64_covers_object_q_ints_decimal
      intervals object_intervals
Proof
  ho_match_mp_tac bounded_object_positive_q_interval64_decimal_list_ind
  >> rw [bounded_object_positive_q_interval64_decimal_list_def,
         compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_positive_q_interval64_decimal_exact
  >> metis_tac []
QED

Theorem bounded_object_positive_q_interval64_decimal_list_covers:
  bounded_object_positive_q_interval64_decimal_list encoded = SOME intervals /\
  bounded_object_q_interval_list encoded = SOME object_intervals /\
  EVERY
    (\object_interval.
      (FST (FST object_interval)) * (SND (SND object_interval)) <=
      (FST (SND object_interval)) * (SND (FST object_interval)))
    object_intervals ==>
  EVERY bounded_interval64_valid intervals /\
  bounded_interval64_list_covers_object_q_decimal intervals encoded
Proof
  strip_tac
  >> imp_res_tac bounded_object_positive_q_interval64_decimal_list_exact
  >> fs [bounded_interval64_list_covers_object_q_decimal_def]
QED

Theorem bounded_object_positive_q_decimal_closed_tests:
  bounded_object_positive_q_floor64_decimal
      (Pair (Pair (Num 1) (Num 0)) (Num 2)) =
    SOME (BoundedSigned64 F 333333333333w) /\
  bounded_object_positive_q_ceil64_decimal
      (Pair (Pair (Num 1) (Num 0)) (Num 2)) =
    SOME (BoundedSigned64 F 333333333334w) /\
  bounded_object_positive_q_interval64_decimal
      (Pair
        (Pair (Pair (Num 1) (Num 0)) (Num 2))
        (Pair (Pair (Num 2) (Num 0)) (Num 2))) =
    SOME
      (BoundedInterval64
        (BoundedSigned64 F 333333333333w)
        (BoundedSigned64 F 666666666667w)) /\
  bounded_object_positive_q_floor64_decimal
      (Pair (Pair (Num 0) (Num 1)) (Num 2)) = NONE
Proof
  EVAL_TAC
  >> wordsLib.WORD_EVAL_TAC
  >> once_rewrite_tac [Q.prove(`(1:num) = SUC 0`, DECIDE_TAC)]
  >> simp (CONJUNCTS
       (DB.fetch "compute_boundedObjectDecimalQ"
          "bounded_object_positive_q_floor64_decimal_compute"))
QED

val _ = export_theory ();
