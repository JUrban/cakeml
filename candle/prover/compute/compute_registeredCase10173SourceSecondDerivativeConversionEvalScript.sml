(*****************************************************************************
 * Exact source-rational conversion for the square-root second derivative.
 *
 * The source evaluator returns the negative reciprocal of the normalized
 * positive product (2 * sqrt(x)) * (2 * x).  This lemma deliberately starts
 * after that product: rational equivalence to the two direct source endpoint
 * products is enough to show that outward decimal conversion is exactly the
 * authenticated packet reciprocal, negated and with endpoints reversed.
 *****************************************************************************)
Theory compute_registeredCase10173SourceSecondDerivativeConversionEval
Ancestors
  compute_boundedCase10173SourceDecimalExact
  compute_registeredCase10173QDecimalEquiv
  compute_registeredCase10173QNegativeConversionEval
Libs
  bossLib preamble wordsLib intLib

Theorem registered_case10173_q_twice_product_source_equiv:
  0 < root_denominator /\ 0 < input_denominator ==>
  bounded_case10173_q_cv_equiv
    (Pair
      (Pair
        (Num
          ((root * root_denominator + root * root_denominator) *
           (input * input_denominator + input * input_denominator)))
        (Num 0))
      (Num
        ((root_denominator * root_denominator) *
          (input_denominator * input_denominator) - 1)))
    (Pair (Pair (Num (4 * root * input)) (Num 0))
      (Num (root_denominator * input_denominator - 1)))
Proof
  strip_tac
  >> `0 < root_denominator * root_denominator` by
       simp [arithmeticTheory.MULT_POS]
  >> `0 < input_denominator * input_denominator` by
       simp [arithmeticTheory.MULT_POS]
  >> `0 <
        (root_denominator * root_denominator) *
          (input_denominator * input_denominator)` by
       simp [arithmeticTheory.MULT_POS]
  >> `0 < root_denominator * input_denominator` by
       simp [arithmeticTheory.MULT_POS]
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred,
        integerTheory.INT_MUL]
  >> INT_RING_TAC
QED

Theorem registered_case10173_source_fraction_cross_reorder:
  (product:num) * (root_denominator * input_denominator) =
      (4 * root * input) * product_denominator ==>
  4 * (input * product_denominator * root) =
    input_denominator * product * root_denominator
Proof
  metis_tac [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_source_sqrt_dd_conversion_eval:
  0 < root_lower /\ 0 < root_lower_denominator /\
  0 < root_upper /\ 0 < root_upper_denominator /\
  0 < input_lower /\ 0 < input_lower_denominator /\
  0 < input_upper /\ 0 < input_upper_denominator /\
  0 < product_lower /\ 0 < product_lower_denominator /\
  0 < product_upper /\ 0 < product_upper_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num product_lower) (Num 0))
      (Num (product_lower_denominator - 1)))
    (Pair
      (Pair (Num (4 * root_lower * input_lower)) (Num 0))
      (Num
        (root_lower_denominator * input_lower_denominator - 1))) /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num product_upper) (Num 0))
      (Num (product_upper_denominator - 1)))
    (Pair
      (Pair (Num (4 * root_upper * input_upper)) (Num 0))
      (Num
        (root_upper_denominator * input_upper_denominator - 1))) /\
  bounded_case10173_source_sqrt_dd_interval64_exact
    (Pair
      (Pair (Pair (Num root_lower) (Num 0))
        (Num (root_lower_denominator - 1)))
      (Pair (Pair (Num root_upper) (Num 0))
        (Num (root_upper_denominator - 1))))
    (Pair
      (Pair (Pair (Num input_lower) (Num 0))
        (Num (input_lower_denominator - 1)))
      (Pair (Pair (Num input_upper) (Num 0))
        (Num (input_upper_denominator - 1))))
    reciprocal /\
  10 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_of_q»
        [from_cv
          (Pair
            (Pair (Pair (Num 0) (Num product_lower_denominator))
              (Num (product_lower - 1)))
            (Pair (Pair (Num 0) (Num product_upper_denominator))
              (Num (product_upper - 1))))]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_interval64_neg reciprocal))),refs)
Proof
  strip_tac
  >> `product_lower *
        (root_lower_denominator * input_lower_denominator) =
      (4 * root_lower * input_lower) * product_lower_denominator` by
       (irule
          compute_registeredCase10173QDecimalEquivTheory.registered_case10173_positive_q_cv_equiv_cross
        >> simp [arithmeticTheory.MULT_POS]
        >> first_assum ACCEPT_TAC)
  >> `product_upper *
        (root_upper_denominator * input_upper_denominator) =
      (4 * root_upper * input_upper) * product_upper_denominator` by
       (irule
          compute_registeredCase10173QDecimalEquivTheory.registered_case10173_positive_q_cv_equiv_cross
        >> simp [arithmeticTheory.MULT_POS]
        >> first_assum ACCEPT_TAC)
  >> `1000000000000 * product_lower_denominator DIV product_lower +
        (if 1000000000000 * product_lower_denominator MOD product_lower = 0
         then 0 else 1) =
      1000000000000 *
          (root_lower_denominator * input_lower_denominator) DIV
          (4 * root_lower * input_lower) +
        (if 1000000000000 *
              (root_lower_denominator * input_lower_denominator) MOD
              (4 * root_lower * input_lower) = 0
         then 0 else 1)` by
       (irule
          compute_registeredCase10173QDecimalEquivTheory.registered_case10173_scaled_fraction_ceil_eq
        >> simp [arithmeticTheory.MULT_POS]
        >> irule registered_case10173_source_fraction_cross_reorder
        >> qpat_x_assum
             `product_lower *
                (root_lower_denominator * input_lower_denominator) = _`
             ACCEPT_TAC)
  >> `1000000000000 * product_upper_denominator DIV product_upper =
      1000000000000 *
        (root_upper_denominator * input_upper_denominator) DIV
        (4 * root_upper * input_upper)` by
       (irule
          compute_registeredCase10173QDecimalEquivTheory.registered_case10173_scaled_fraction_floor_eq
        >> simp [arithmeticTheory.MULT_POS]
        >> irule registered_case10173_source_fraction_cross_reorder
        >> qpat_x_assum
             `product_upper *
                (root_upper_denominator * input_upper_denominator) = _`
             ACCEPT_TAC)
  >> Cases_on `reciprocal`
  >> rename1 `BoundedInterval64 lower_endpoint upper_endpoint`
  >> Cases_on `lower_endpoint`
  >> Cases_on `upper_endpoint`
  >> rename1
       `BoundedInterval64
          (BoundedSigned64 lower_negative lower_word)
          (BoundedSigned64 upper_negative upper_word)`
  >> `SUC (input_lower_denominator - 1) = input_lower_denominator` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> first_assum ACCEPT_TAC)
  >> `SUC (root_lower_denominator - 1) = root_lower_denominator` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> first_assum ACCEPT_TAC)
  >> `SUC (input_upper_denominator - 1) = input_upper_denominator` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> first_assum ACCEPT_TAC)
  >> `SUC (root_upper_denominator - 1) = root_upper_denominator` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> first_assum ACCEPT_TAC)
  >> `SUC (product_lower - 1) = product_lower` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> first_assum ACCEPT_TAC)
  >> `SUC (product_upper - 1) = product_upper` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> first_assum ACCEPT_TAC)
  >> fs
       [compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_interval64_exact_def,
        compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_floor64_exact_def,
        compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_ceil64_exact_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred]
  >> mp_tac
       (Q.INST
         [`lower_value` |-> `product_lower_denominator`,
          `lower_denominator_minus_one` |-> `product_lower - 1`,
          `upper_value` |-> `product_upper_denominator`,
          `upper_denominator_minus_one` |-> `product_upper - 1`,
          `clock` |-> `clock`, `refs` |-> `refs`]
         compute_registeredCase10173QNegativeConversionEvalTheory.registered_case10173_fs_interval_of_q_negative_eval)
  >> impl_tac >- simp []
  >> strip_tac
  >> asm_rewrite_tac []
  >> Cases_on `lower_word = 0w`
  >> Cases_on `upper_word = 0w`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def]
QED

val _ = export_theory ();
