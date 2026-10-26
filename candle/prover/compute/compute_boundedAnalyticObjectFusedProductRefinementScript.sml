(*****************************************************************************
 * Object-q refinement for the fused scale-2^40 Taylor product accumulator.
 *
 * The production product rule accumulates raw scale-2^80 products and rounds
 * only after the whole sum.  This theory relates those unrounded raw bounds
 * directly to exact source rationals; it does not insert weaker per-product
 * fixed-point rounding steps that the executable checker never performs.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectFusedProductRefinement
Ancestors
  compute_boundedAnalyticObjectProductRefinement compute_boundedTaylorMul
Libs
  bossLib preamble intLib

Definition bounded_fused_raw_interval_contains_int_fraction_def:
  bounded_fused_raw_interval_contains_int_fraction
      (lower,upper) ((numerator,denominator):int # int) <=>
    0 < denominator /\
    denominator * bounded_signed192_to_int lower <=
      (&1099511627776:int) * (&1099511627776:int) * numerator /\
    (&1099511627776:int) * (&1099511627776:int) * numerator <=
      denominator * bounded_signed192_to_int upper
End

Theorem bounded_int_positive_scales_raw_product_corner:
  0 < (left_scale:int) /\ 0 < right_scale /\
  output_lower <= left * right /\
  left * right <= output_upper ==>
  left_scale * right_scale * output_lower <=
      (left_scale * left) * (right_scale * right) /\
  (left_scale * left) * (right_scale * right) <=
      left_scale * right_scale * output_upper
Proof
  strip_tac
  >> `0 <= left_scale * right_scale` by
       (irule integerTheory.INT_LE_MUL >> intLib.ARITH_TAC)
  >> `(left_scale * right_scale) * output_lower <=
      (left_scale * right_scale) * (left * right)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> `(left_scale * right_scale) * (left * right) <=
      (left_scale * right_scale) * output_upper` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> `(left_scale * left) * (right_scale * right) =
      (left_scale * right_scale) * (left * right)` by INT_RING_TAC
  >> metis_tac []
QED

Theorem bounded_interval64_raw_mul_bounds_contains_int_fraction_product:
  bounded_interval64_valid left /\
  bounded_interval64_valid right /\
  bounded_interval64_contains_int_fraction left left_fraction /\
  bounded_interval64_contains_int_fraction right right_fraction ==>
  bounded_fused_raw_interval_contains_int_fraction
    (let raw = bounded_interval64_raw_mul_bounds_unchecked left right in
       (bounded_signed128_widen192 (FST raw),
        bounded_signed128_widen192 (SND raw)))
    (bounded_int_fraction_mul left_fraction right_fraction)
Proof
  PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_interval64_valid
          (BoundedInterval64 left_lower left_upper) /\
        bounded_interval64_valid
          (BoundedInterval64 right_lower right_upper) /\ _`
  >> strip_tac
  >> `bounded_signed64_to_int left_lower <=
        bounded_signed64_to_int left_upper /\
      bounded_signed64_to_int right_lower <=
        bounded_signed64_to_int right_upper` by
       fs [compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> `bounded_interval64_contains_int
        (BoundedInterval64 left_lower left_upper)
          (bounded_signed64_to_int left_lower) /\
      bounded_interval64_contains_int
        (BoundedInterval64 left_lower left_upper)
          (bounded_signed64_to_int left_upper) /\
      bounded_interval64_contains_int
        (BoundedInterval64 right_lower right_upper)
          (bounded_signed64_to_int right_lower) /\
      bounded_interval64_contains_int
        (BoundedInterval64 right_lower right_upper)
          (bounded_signed64_to_int right_upper)` by
       simp [compute_boundedIntervalTheory.bounded_interval64_contains_int_def]
  >> qabbrev_tac `raw =
        bounded_interval64_raw_mul_bounds_unchecked
          (BoundedInterval64 left_lower left_upper)
          (BoundedInterval64 right_lower right_upper)`
  >> `bounded_signed128_to_int (FST raw) <=
        bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower /\
      bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower <=
        bounded_signed128_to_int (SND raw)` by
       metis_tac
         [compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_contains_product]
  >> `bounded_signed128_to_int (FST raw) <=
        bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper /\
      bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper <=
        bounded_signed128_to_int (SND raw)` by
       metis_tac
         [compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_contains_product]
  >> `bounded_signed128_to_int (FST raw) <=
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower /\
      bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower <=
        bounded_signed128_to_int (SND raw)` by
       metis_tac
         [compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_contains_product]
  >> `bounded_signed128_to_int (FST raw) <=
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper /\
      bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper <=
        bounded_signed128_to_int (SND raw)` by
       metis_tac
         [compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_contains_product]
  >> `0 < left_fraction1 /\ 0 < right_fraction1` by
       fs [bounded_interval64_contains_int_fraction_def]
  >> `left_fraction1 * right_fraction1 *
        bounded_signed128_to_int (FST raw) <=
        (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_lower) /\
      (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_lower) <=
        left_fraction1 * right_fraction1 *
          bounded_signed128_to_int (SND raw)` by
       metis_tac [bounded_int_positive_scales_raw_product_corner]
  >> `left_fraction1 * right_fraction1 *
        bounded_signed128_to_int (FST raw) <=
        (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_upper) /\
      (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_upper) <=
        left_fraction1 * right_fraction1 *
          bounded_signed128_to_int (SND raw)` by
       metis_tac [bounded_int_positive_scales_raw_product_corner]
  >> `left_fraction1 * right_fraction1 *
        bounded_signed128_to_int (FST raw) <=
        (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_lower) /\
      (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_lower) <=
        left_fraction1 * right_fraction1 *
          bounded_signed128_to_int (SND raw)` by
       metis_tac [bounded_int_positive_scales_raw_product_corner]
  >> `left_fraction1 * right_fraction1 *
        bounded_signed128_to_int (FST raw) <=
        (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_upper) /\
      (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_upper) <=
        left_fraction1 * right_fraction1 *
          bounded_signed128_to_int (SND raw)` by
       metis_tac [bounded_int_positive_scales_raw_product_corner]
  >> mp_tac
       (INST
         [``left_lower:int`` |->
            ``left_fraction1 * bounded_signed64_to_int left_lower``,
          ``left_value:int`` |->
            ``(&1099511627776:int) * left_fraction0``,
          ``left_upper:int`` |->
            ``left_fraction1 * bounded_signed64_to_int left_upper``,
          ``right_lower:int`` |->
            ``right_fraction1 * bounded_signed64_to_int right_lower``,
          ``right_value:int`` |->
            ``(&1099511627776:int) * right_fraction0``,
          ``right_upper:int`` |->
            ``right_fraction1 * bounded_signed64_to_int right_upper``]
         compute_boundedIntervalTheory.bounded_int_product_bounds_corners)
  >> fs [bounded_interval64_contains_int_fraction_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> simp []
  >> disch_then assume_tac
  >> `left_fraction1 * right_fraction1 *
        bounded_signed128_to_int (FST raw) <=
        ((&1099511627776:int) * left_fraction0) *
          ((&1099511627776:int) * right_fraction0) /\
      ((&1099511627776:int) * left_fraction0) *
          ((&1099511627776:int) * right_fraction0) <=
        left_fraction1 * right_fraction1 *
          bounded_signed128_to_int (SND raw)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_four_corners_enclose
        >> qexists_tac
             `(left_fraction1 * bounded_signed64_to_int left_lower) *
                (right_fraction1 * bounded_signed64_to_int right_lower)`
        >> qexists_tac
             `(left_fraction1 * bounded_signed64_to_int left_lower) *
                (right_fraction1 * bounded_signed64_to_int right_upper)`
        >> qexists_tac
             `(left_fraction1 * bounded_signed64_to_int left_upper) *
                (right_fraction1 * bounded_signed64_to_int right_lower)`
        >> qexists_tac
             `(left_fraction1 * bounded_signed64_to_int left_upper) *
                (right_fraction1 * bounded_signed64_to_int right_upper)`
        >> asm_rewrite_tac [])
  >> simp
       [bounded_fused_raw_interval_contains_int_fraction_def,
        bounded_int_fraction_mul_def,
        compute_boundedTaylorMulTheory.bounded_signed128_widen192_value]
  >> conj_tac
  >- (irule
        (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
      >> simp [])
  >> `1208925819614629174706176 *
        (left_fraction0 * right_fraction0) =
      (&1099511627776:int) * left_fraction0 *
        ((&1099511627776:int) * right_fraction0)` by INT_RING_TAC
  >> asm_rewrite_tac []
QED

Definition bounded_int_fraction_add_def:
  bounded_int_fraction_add
      ((left_numerator,left_denominator):int # int)
      ((right_numerator,right_denominator):int # int) =
    (left_numerator * right_denominator +
       right_numerator * left_denominator,
     left_denominator * right_denominator)
End

Theorem bounded_fused_raw_interval_add_contains_int_fraction:
  bounded_fused_raw_interval_contains_int_fraction left left_fraction /\
  bounded_fused_raw_interval_contains_int_fraction right right_fraction /\
  bounded_signed192_add (FST left) (FST right) = SOME lower /\
  bounded_signed192_add (SND left) (SND right) = SOME upper ==>
  bounded_fused_raw_interval_contains_int_fraction
    (lower,upper)
    (bounded_int_fraction_add left_fraction right_fraction)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> rw [bounded_fused_raw_interval_contains_int_fraction_def,
         bounded_int_fraction_add_def]
  >> imp_res_tac
       compute_boundedWideSignedTheory.bounded_signed192_add_value
  >> gvs []
  >> FIRST
       [irule
          compute_boundedAnalyticObjectRefinementTheory.bounded_int_fraction_add_lower_bound
        >> simp [],
        irule
          compute_boundedAnalyticObjectRefinementTheory.bounded_int_fraction_add_upper_bound
        >> simp [],
        irule
          (REWRITE_RULE [integerTheory.INT_0] integerTheory.INT_LT_MUL)
        >> simp []]
QED

Definition bounded_fused_product_input_represents_int_fraction_def:
  bounded_fused_product_input_represents_int_fraction
      (left,right) exact_fraction <=>
    ?left_fraction right_fraction.
      bounded_interval64_contains_int_fraction left left_fraction /\
      bounded_interval64_contains_int_fraction right right_fraction /\
      exact_fraction =
        bounded_int_fraction_mul left_fraction right_fraction
End

Definition bounded_int_fraction_sum_acc_def:
  bounded_int_fraction_sum_acc [] accumulator = accumulator /\
  bounded_int_fraction_sum_acc (value::rest) accumulator =
    bounded_int_fraction_sum_acc rest
      (bounded_int_fraction_add accumulator value)
End

Theorem bounded_interval64_raw_sum_acc_contains_int_fraction:
  !products exact_fractions lower upper accumulator_fraction result.
    LIST_REL bounded_fused_product_input_represents_int_fraction
      products exact_fractions /\
    bounded_fused_raw_interval_contains_int_fraction
      (lower,upper) accumulator_fraction /\
    bounded_interval64_raw_sum_acc products lower upper = SOME result ==>
    bounded_fused_raw_interval_contains_int_fraction result
      (bounded_int_fraction_sum_acc
        exact_fractions accumulator_fraction)
Proof
  Induct
  >- (Cases_on `exact_fractions`
      >> gvs
           [compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def,
            bounded_int_fraction_sum_acc_def, LIST_REL_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `exact_fractions`
  >> rw
       [compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def,
        bounded_int_fraction_sum_acc_def, LIST_REL_def]
  >> every_case_tac
  >> gvs
       [LIST_REL_def,
        bounded_fused_product_input_represents_int_fraction_def]
  >> `bounded_fused_raw_interval_contains_int_fraction
        (bounded_signed128_widen192
           (FST (bounded_interval64_raw_mul_bounds_unchecked h0 h1)),
         bounded_signed128_widen192
           (SND (bounded_interval64_raw_mul_bounds_unchecked h0 h1)))
        (bounded_int_fraction_mul left_fraction right_fraction)` by
       (match_mp_tac
          (SIMP_RULE (srw_ss()) [LET_THM]
            (Q.INST
              [`left` |-> `h0`, `right` |-> `h1`,
               `left_fraction` |-> `left_fraction`,
               `right_fraction` |-> `right_fraction`]
              bounded_interval64_raw_mul_bounds_contains_int_fraction_product))
        >> simp [])
  >> `bounded_fused_raw_interval_contains_int_fraction
        (x',x)
        (bounded_int_fraction_add accumulator_fraction
          (bounded_int_fraction_mul left_fraction right_fraction))` by
       (match_mp_tac
          (Q.INST
            [`left` |-> `(lower,upper)`,
             `right` |->
               `(bounded_signed128_widen192
                   (FST (bounded_interval64_raw_mul_bounds_unchecked h0 h1)),
                 bounded_signed128_widen192
                   (SND (bounded_interval64_raw_mul_bounds_unchecked h0 h1)))`,
             `left_fraction` |-> `accumulator_fraction`,
             `right_fraction` |->
               `bounded_int_fraction_mul left_fraction right_fraction`,
             `lower` |-> `x'`, `upper` |-> `x`]
            bounded_fused_raw_interval_add_contains_int_fraction)
        >> simp [])
  >> qpat_x_assum
       `!exact_fractions lower upper accumulator_fraction result. _`
       (mp_tac o Q.SPECL
          [`t`, `x'`, `x`,
           `bounded_int_fraction_add accumulator_fraction
             (bounded_int_fraction_mul left_fraction right_fraction)`,
           `result`])
  >> simp []
QED

Theorem bounded_scale40_cancel_fraction_round:
  0 < (denominator:int) /\
  denominator * ((&1099511627776:int) * output_lower) <=
    (&1099511627776:int) * (&1099511627776:int) * numerator /\
  (&1099511627776:int) * (&1099511627776:int) * numerator <=
    denominator * ((&1099511627776:int) * output_upper) ==>
  denominator * output_lower <=
    (&1099511627776:int) * numerator /\
  (&1099511627776:int) * numerator <=
    denominator * output_upper
Proof
  strip_tac
  >> `denominator * ((&1099511627776:int) * output_lower) =
      (&1099511627776:int) * (denominator * output_lower)` by
       INT_RING_TAC
  >> `(&1099511627776:int) * (&1099511627776:int) * numerator =
      (&1099511627776:int) *
        ((&1099511627776:int) * numerator)` by INT_RING_TAC
  >> `denominator * ((&1099511627776:int) * output_upper) =
      (&1099511627776:int) * (denominator * output_upper)` by
       INT_RING_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_fused_raw_round40_contains_int_fraction:
  bounded_fused_raw_interval_contains_int_fraction
      (raw_lower,raw_upper) (numerator,denominator) /\
  bounded_signed192_shift_floor40_64 raw_lower = SOME lower /\
  bounded_signed192_shift_ceil40_64 raw_upper = SOME upper ==>
  bounded_interval64_contains_int_fraction
    (BoundedInterval64 lower upper) (numerator,denominator)
Proof
  rw [bounded_fused_raw_interval_contains_int_fraction_def,
      bounded_interval64_contains_int_fraction_def,
      compute_boundedIntervalTheory.bounded_interval64_lower_def,
      compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> imp_res_tac
       compute_boundedTaylorMulTheory.bounded_signed192_shift_floor40_64_lower_bound
  >> imp_res_tac
       compute_boundedTaylorMulTheory.bounded_signed192_shift_ceil40_64_upper_bound
  >> `denominator *
        ((&1099511627776:int) * bounded_signed64_to_int lower) <=
      denominator * bounded_signed192_to_int raw_lower` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> `denominator * bounded_signed192_to_int raw_upper <=
      denominator *
        ((&1099511627776:int) * bounded_signed64_to_int upper)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> `denominator *
        ((&1099511627776:int) * bounded_signed64_to_int lower) <=
      (&1099511627776:int) * (&1099511627776:int) * numerator` by
       intLib.ARITH_TAC
  >> `(&1099511627776:int) * (&1099511627776:int) * numerator <=
      denominator *
        ((&1099511627776:int) * bounded_signed64_to_int upper)` by
       intLib.ARITH_TAC
  >> metis_tac [bounded_scale40_cancel_fraction_round]
QED

Theorem bounded_fused_raw_zero_contains_int_fraction:
  bounded_fused_raw_interval_contains_int_fraction
    (bounded_signed192_make F bounded192_zero,
     bounded_signed192_make F bounded192_zero)
    (0,1)
Proof
  simp [bounded_fused_raw_interval_contains_int_fraction_def,
        compute_boundedWideSignedTheory.bounded_signed192_make_value,
        compute_boundedWideTheory.bounded192_zero_def,
        compute_boundedTheory.bounded192_to_num_def]
QED

Theorem bounded_interval64_fused_products_contains_int_fraction:
  LIST_REL bounded_fused_product_input_represents_int_fraction
      products exact_fractions /\
  bounded_interval64_fused_products products = SOME result ==>
  bounded_interval64_contains_int_fraction result
    (bounded_int_fraction_sum_acc exact_fractions (0,1))
Proof
  rw [compute_boundedTaylorMulTheory.bounded_interval64_fused_products_def,
      LET_THM]
  >> every_case_tac
  >> gvs []
  >> assume_tac bounded_fused_raw_zero_contains_int_fraction
  >> imp_res_tac bounded_interval64_raw_sum_acc_contains_int_fraction
  >> Cases_on
       `bounded_int_fraction_sum_acc exact_fractions (0,1)`
  >> gvs []
  >> imp_res_tac bounded_fused_raw_round40_contains_int_fraction
QED

val _ = export_theory ();
