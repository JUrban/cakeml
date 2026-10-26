(*****************************************************************************
 * Source-rational soundness for generic bounded analytic preparation.
 *
 * The contract uses exact integer cross multiplication.  It therefore says
 * directly that the stored scale-2^40 endpoints enclose the original source
 * rational, without introducing real division or trusting the compiler's
 * rounding implementation.
 *****************************************************************************)
Theory compute_boundedAnalyticPreparedPlanSound
Ancestors
  compute_boundedAnalyticPreparedPlan
Libs
  bossLib preamble intLib wordsLib

Definition bounded_analytic_rational_interval_covers_def:
  bounded_analytic_rational_interval_covers positive negative
      denominator_predecessor interval <=>
    let denominator = SUC denominator_predecessor;
        source_numerator = (&positive:int) - &negative;
        scale = (&bounded_analytic_scale40:int)
    in
      bounded_interval64_valid interval /\
      (&denominator:int) *
          bounded_signed64_to_int (bounded_interval64_lower interval) <=
        scale * source_numerator /\
      scale * source_numerator <=
        (&denominator:int) *
          bounded_signed64_to_int (bounded_interval64_upper interval)
End

Theorem bounded_analytic_nat_ceil_div_eq:
  0 < denominator ==>
  bounded_analytic_nat_ceil_div numerator denominator =
    CEILING_DIV numerator denominator
Proof
  rw [bounded_analytic_nat_ceil_div_def]
  >> Cases_on `numerator MOD denominator = 0`
  >- simp [arithmeticTheory.CEILING_DIV]
  >> `0 < numerator MOD denominator` by simp []
  >> simp [arithmeticTheory.CEILING_DIV,MIN_DEF]
QED

Theorem bounded_analytic_nat_floor_ceil_bounds:
  0 < denominator ==>
  denominator * (numerator DIV denominator) <= numerator /\
  numerator <= denominator *
    bounded_analytic_nat_ceil_div numerator denominator
Proof
  strip_tac
  >> conj_tac
  >- metis_tac [arithmeticTheory.X_LE_DIV, arithmeticTheory.LE_REFL,
                 arithmeticTheory.MULT_COMM]
  >> simp [bounded_analytic_nat_ceil_div_eq]
  >> metis_tac [arithmeticTheory.LE_MULT_CEILING_DIV,
                 arithmeticTheory.MULT_COMM]
QED

Theorem bounded_analytic_nat_floor_le_ceil:
  0 < denominator ==>
  numerator DIV denominator <=
    bounded_analytic_nat_ceil_div numerator denominator
Proof
  simp [bounded_analytic_nat_ceil_div_def]
  >> every_case_tac >> simp []
QED

Theorem bounded_analytic_nonnegative_interval64_values:
  floor_magnitude <= ceiling_magnitude /\
  ceiling_magnitude < 18446744073709551616 ==>
  bounded_interval64_valid
    (BoundedInterval64
      (bounded_signed64_make F (n2w floor_magnitude))
      (bounded_signed64_make F (n2w ceiling_magnitude))) /\
  bounded_signed64_to_int
      (bounded_interval64_lower
        (BoundedInterval64
          (bounded_signed64_make F (n2w floor_magnitude))
          (bounded_signed64_make F (n2w ceiling_magnitude)))) =
    &floor_magnitude /\
  bounded_signed64_to_int
      (bounded_interval64_upper
        (BoundedInterval64
          (bounded_signed64_make F (n2w floor_magnitude))
          (bounded_signed64_make F (n2w ceiling_magnitude)))) =
    &ceiling_magnitude
Proof
  strip_tac
  >> `floor_magnitude < 18446744073709551616` by intLib.ARITH_TAC
  >> simp [compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_make_normalized,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
           compute_boundedSignedEndpointTheory.bounded_signed64_make_value,
           wordsTheory.w2n_n2w, wordsTheory.dimword_64]
QED

Theorem bounded_analytic_negative_interval64_values:
  floor_magnitude <= ceiling_magnitude /\
  ceiling_magnitude < 18446744073709551616 ==>
  bounded_interval64_valid
    (BoundedInterval64
      (bounded_signed64_make T (n2w ceiling_magnitude))
      (bounded_signed64_make T (n2w floor_magnitude))) /\
  bounded_signed64_to_int
      (bounded_interval64_lower
        (BoundedInterval64
          (bounded_signed64_make T (n2w ceiling_magnitude))
          (bounded_signed64_make T (n2w floor_magnitude)))) =
    -&ceiling_magnitude /\
  bounded_signed64_to_int
      (bounded_interval64_upper
        (BoundedInterval64
          (bounded_signed64_make T (n2w ceiling_magnitude))
          (bounded_signed64_make T (n2w floor_magnitude)))) =
    -&floor_magnitude
Proof
  strip_tac
  >> `floor_magnitude < 18446744073709551616` by intLib.ARITH_TAC
  >> simp [compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_make_normalized,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
           compute_boundedSignedEndpointTheory.bounded_signed64_make_value,
           wordsTheory.w2n_n2w, wordsTheory.dimword_64]
  >> intLib.ARITH_TAC
QED

Theorem bounded_analytic_int_negative_difference:
  positive < negative ==>
  (&positive:int) - &negative = -&(negative - positive)
Proof
  strip_tac
  >> `positive <= negative` by DECIDE_TAC
  >> ONCE_REWRITE_TAC [GSYM integerTheory.INT_NEG_SUB]
  >> simp [integerTheory.INT_SUB]
QED

Theorem bounded_analytic_int_nonnegative_difference:
  ~(positive < negative) ==>
  (&positive:int) - &negative = &(positive - negative)
Proof
  strip_tac
  >> `negative <= positive` by DECIDE_TAC
  >> simp [integerTheory.INT_SUB]
QED

Theorem bounded_analytic_rational_constant64_covers:
  bounded_analytic_rational_constant64 positive negative
      denominator_predecessor = SOME interval ==>
  bounded_analytic_rational_interval_covers positive negative
      denominator_predecessor interval
Proof
  Cases_on `positive < negative`
  >> rw [bounded_analytic_rational_constant64_def]
  >> gvs [LET_THM]
  >- (
    assume_tac
      (Q.INST
        [`numerator` |->
           `bounded_analytic_scale40 * (negative - positive)`,
         `denominator` |-> `SUC denominator_predecessor`]
        bounded_analytic_nat_floor_ceil_bounds)
    >> assume_tac
      (Q.INST
        [`numerator` |->
           `bounded_analytic_scale40 * (negative - positive)`,
         `denominator` |-> `SUC denominator_predecessor`]
        bounded_analytic_nat_floor_le_ceil)
    >> assume_tac
      (Q.INST
        [`floor_magnitude` |->
           `bounded_analytic_scale40 * (negative - positive) DIV
              SUC denominator_predecessor`,
         `ceiling_magnitude` |->
           `bounded_analytic_nat_ceil_div
              (bounded_analytic_scale40 * (negative - positive))
              (SUC denominator_predecessor)`]
        bounded_analytic_negative_interval64_values)
    >> assume_tac
      (Q.INST [`positive` |-> `positive`, `negative` |-> `negative`]
        bounded_analytic_int_negative_difference)
    >> fs [bounded_analytic_rational_interval_covers_def,
           bounded_analytic_scale40_def]
    >> `(&1099511627776:int) * &(negative - positive) <=
          &SUC denominator_predecessor *
          &bounded_analytic_nat_ceil_div
            (1099511627776 * (negative - positive))
            (SUC denominator_predecessor)` by
         metis_tac [integerTheory.INT_OF_NUM_LE,
                    integerTheory.INT_OF_NUM_MUL]
    >> `&SUC denominator_predecessor *
          &(1099511627776 * (negative - positive) DIV
            SUC denominator_predecessor) <=
          (&1099511627776:int) * &(negative - positive)` by
         metis_tac [integerTheory.INT_OF_NUM_LE,
                    integerTheory.INT_OF_NUM_MUL]
    >> intLib.ARITH_TAC)
  >> assume_tac
    (Q.INST
      [`numerator` |->
         `bounded_analytic_scale40 * (positive - negative)`,
       `denominator` |-> `SUC denominator_predecessor`]
      bounded_analytic_nat_floor_ceil_bounds)
  >> assume_tac
    (Q.INST
      [`numerator` |->
         `bounded_analytic_scale40 * (positive - negative)`,
       `denominator` |-> `SUC denominator_predecessor`]
      bounded_analytic_nat_floor_le_ceil)
  >> assume_tac
    (Q.INST
      [`floor_magnitude` |->
         `bounded_analytic_scale40 * (positive - negative) DIV
            SUC denominator_predecessor`,
       `ceiling_magnitude` |->
         `bounded_analytic_nat_ceil_div
            (bounded_analytic_scale40 * (positive - negative))
            (SUC denominator_predecessor)`]
      bounded_analytic_nonnegative_interval64_values)
  >> assume_tac
    (Q.INST [`positive` |-> `positive`, `negative` |-> `negative`]
      bounded_analytic_int_nonnegative_difference)
  >> fs [bounded_analytic_rational_interval_covers_def,
         bounded_analytic_scale40_def]
QED

val _ = export_theory ();
