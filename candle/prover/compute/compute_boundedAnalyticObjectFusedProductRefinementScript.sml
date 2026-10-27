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

Theorem bounded_int_fraction_min4_member:
  bounded_int_fraction_min4 q1 q2 q3 q4 = q1 \/
  bounded_int_fraction_min4 q1 q2 q3 q4 = q2 \/
  bounded_int_fraction_min4 q1 q2 q3 q4 = q3 \/
  bounded_int_fraction_min4 q1 q2 q3 q4 = q4
Proof
  rw [bounded_int_fraction_min4_def,
      bounded_int_fraction_min_def]
QED

Theorem bounded_int_fraction_max4_member:
  bounded_int_fraction_max4 q1 q2 q3 q4 = q1 \/
  bounded_int_fraction_max4 q1 q2 q3 q4 = q2 \/
  bounded_int_fraction_max4 q1 q2 q3 q4 = q3 \/
  bounded_int_fraction_max4 q1 q2 q3 q4 = q4
Proof
  rw [bounded_int_fraction_max4_def,
      bounded_int_fraction_max_def]
QED

Definition bounded_fused_product_input_covers_object_q_ints_def:
  bounded_fused_product_input_covers_object_q_ints
      (left,right) (left_object_interval,right_object_interval) <=>
    bounded_interval64_covers_object_q_ints
      left left_object_interval /\
    bounded_interval64_covers_object_q_ints
      right right_object_interval
End

Definition bounded_object_q_interval_product_lower_ints_def:
  bounded_object_q_interval_product_lower_ints
      (left_object_interval,right_object_interval) =
    FST
      (bounded_object_q_interval_mul_ints
        left_object_interval right_object_interval)
End

Definition bounded_object_q_interval_product_upper_ints_def:
  bounded_object_q_interval_product_upper_ints
      (left_object_interval,right_object_interval) =
    SND
      (bounded_object_q_interval_mul_ints
        left_object_interval right_object_interval)
End

Theorem bounded_fused_product_input_covers_object_q_ints_endpoints:
  bounded_fused_product_input_covers_object_q_ints
      input object_input ==>
  bounded_fused_product_input_represents_int_fraction input
      (bounded_object_q_interval_product_lower_ints object_input) /\
  bounded_fused_product_input_represents_int_fraction input
      (bounded_object_q_interval_product_upper_ints object_input)
Proof
  PairCases_on `input`
  >> PairCases_on `object_input`
  >> rw
       [bounded_fused_product_input_covers_object_q_ints_def,
        bounded_object_q_interval_product_lower_ints_def,
        bounded_object_q_interval_product_upper_ints_def]
  >> imp_res_tac
       bounded_interval64_covers_object_q_ints_contains_endpoints
  >> fs [bounded_object_q_interval_mul_ints_def,
         bounded_fused_product_input_represents_int_fraction_def]
  >> rw [bounded_int_fraction_min4_def,
         bounded_int_fraction_max4_def,
         bounded_int_fraction_min_def,
         bounded_int_fraction_max_def]
  >> metis_tac []
QED

Theorem bounded_fused_product_inputs_covers_object_q_ints_endpoints:
  !products object_products.
    LIST_REL bounded_fused_product_input_covers_object_q_ints
      products object_products ==>
    LIST_REL bounded_fused_product_input_represents_int_fraction
      products
      (MAP bounded_object_q_interval_product_lower_ints object_products) /\
    LIST_REL bounded_fused_product_input_represents_int_fraction
      products
      (MAP bounded_object_q_interval_product_upper_ints object_products)
Proof
  Induct
  >> Cases_on `object_products`
  >> rw [LIST_REL_def]
  >> res_tac
  >> imp_res_tac
       bounded_fused_product_input_covers_object_q_ints_endpoints
  >> simp [LIST_REL_def]
QED

Definition bounded_object_q_interval_products_sum_acc_ints_def:
  bounded_object_q_interval_products_sum_acc_ints [] accumulator =
      accumulator /\
  bounded_object_q_interval_products_sum_acc_ints
      (object_input::object_inputs) accumulator =
    bounded_object_q_interval_products_sum_acc_ints object_inputs
      (bounded_object_q_interval_add_ints accumulator
        (bounded_object_q_interval_mul_ints
          (FST object_input) (SND object_input)))
End

Theorem bounded_object_q_interval_add_ints_components:
  FST (bounded_object_q_interval_add_ints left right) =
      bounded_int_fraction_add (FST left) (FST right) /\
  SND (bounded_object_q_interval_add_ints left right) =
      bounded_int_fraction_add (SND left) (SND right)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_interval_add_ints_def,
        bounded_int_fraction_add_def]
QED

Theorem bounded_object_q_interval_products_sum_acc_ints_components:
  !object_inputs accumulator.
    bounded_object_q_interval_products_sum_acc_ints
      object_inputs accumulator =
    (bounded_int_fraction_sum_acc
       (MAP bounded_object_q_interval_product_lower_ints object_inputs)
       (FST accumulator),
     bounded_int_fraction_sum_acc
       (MAP bounded_object_q_interval_product_upper_ints object_inputs)
       (SND accumulator))
Proof
  Induct
  >- simp [bounded_object_q_interval_products_sum_acc_ints_def,
           bounded_int_fraction_sum_acc_def]
  >> gen_tac
  >> PairCases_on `h`
  >> gen_tac
  >> Cases_on `accumulator`
  >> PairCases_on `q`
  >> PairCases_on `r`
  >> simp
       [bounded_object_q_interval_products_sum_acc_ints_def,
        bounded_int_fraction_sum_acc_def,
        bounded_object_q_interval_product_lower_ints_def,
        bounded_object_q_interval_product_upper_ints_def,
        bounded_object_q_interval_mul_ints_def,
        bounded_object_q_interval_add_ints_components,
        bounded_int_fraction_add_def]
QED

Definition bounded_int_fraction_interval_valid_def:
  bounded_int_fraction_interval_valid (lower,upper) <=>
    bounded_int_fraction_positive lower /\
    bounded_int_fraction_positive upper /\
    bounded_int_fraction_le lower upper
End

Theorem bounded_interval64_covers_object_q_ints_valid:
  bounded_interval64_covers_object_q_ints interval object_interval ==>
  bounded_int_fraction_interval_valid object_interval
Proof
  PairCases_on `object_interval`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_ints_def,
        bounded_int_fraction_interval_valid_def,
        bounded_int_fraction_positive_def,
        bounded_int_fraction_le_def]
QED

Theorem bounded_int_fraction_mul_positive:
  bounded_int_fraction_positive left /\
  bounded_int_fraction_positive right ==>
  bounded_int_fraction_positive
    (bounded_int_fraction_mul left right)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> simp [bounded_int_fraction_positive_def,
           bounded_int_fraction_mul_def,
           integerTheory.INT_MUL_SIGN_CASES]
QED

Theorem bounded_int_fraction_add_positive:
  bounded_int_fraction_positive left /\
  bounded_int_fraction_positive right ==>
  bounded_int_fraction_positive
    (bounded_int_fraction_add left right)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> simp [bounded_int_fraction_positive_def,
           bounded_int_fraction_add_def,
           integerTheory.INT_MUL_SIGN_CASES]
QED

Theorem bounded_int_fraction_add_le:
  bounded_int_fraction_positive left_lower /\
  bounded_int_fraction_positive left_upper /\
  bounded_int_fraction_le left_lower left_upper /\
  bounded_int_fraction_positive right_lower /\
  bounded_int_fraction_positive right_upper /\
  bounded_int_fraction_le right_lower right_upper ==>
  bounded_int_fraction_le
    (bounded_int_fraction_add left_lower right_lower)
    (bounded_int_fraction_add left_upper right_upper)
Proof
  PairCases_on `left_lower`
  >> PairCases_on `left_upper`
  >> PairCases_on `right_lower`
  >> PairCases_on `right_upper`
  >> fs [bounded_int_fraction_positive_def,
         bounded_int_fraction_le_def,
         bounded_int_fraction_add_def]
  >> metis_tac
       [compute_boundedAnalyticObjectRefinementTheory.bounded_int_fraction_interval_add_ordered]
QED

Theorem bounded_object_q_interval_mul_ints_valid:
  bounded_int_fraction_interval_valid left /\
  bounded_int_fraction_interval_valid right ==>
  bounded_int_fraction_interval_valid
    (bounded_object_q_interval_mul_ints left right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp [bounded_int_fraction_interval_valid_def]
  >> strip_tac
  >> `bounded_int_fraction_positive
        (bounded_int_fraction_mul q q') /\
      bounded_int_fraction_positive
        (bounded_int_fraction_mul q r') /\
      bounded_int_fraction_positive
        (bounded_int_fraction_mul r q') /\
      bounded_int_fraction_positive
        (bounded_int_fraction_mul r r')` by
       metis_tac [bounded_int_fraction_mul_positive]
  >> simp [bounded_object_q_interval_mul_ints_def,
           bounded_int_fraction_interval_valid_def]
  >> metis_tac
       [bounded_int_fraction_min4_positive,
        bounded_int_fraction_max4_positive,
        bounded_int_fraction_min4_le_max4]
QED

Theorem bounded_object_q_interval_add_ints_valid:
  bounded_int_fraction_interval_valid left /\
  bounded_int_fraction_interval_valid right ==>
  bounded_int_fraction_interval_valid
    (bounded_object_q_interval_add_ints left right)
Proof
  PairCases_on `left`
  >> PairCases_on `right`
  >> fs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_interval_add_ints_def,
        bounded_int_fraction_interval_valid_def,
        bounded_int_fraction_positive_def,
        bounded_int_fraction_le_def]
  >> strip_tac
  >> conj_tac
  >- fs [integerTheory.INT_MUL_SIGN_CASES]
  >> conj_tac
  >- fs [integerTheory.INT_MUL_SIGN_CASES]
  >> metis_tac
       [compute_boundedAnalyticObjectRefinementTheory.bounded_int_fraction_interval_add_ordered]
QED

Theorem bounded_object_q_interval_products_sum_acc_ints_valid:
  !object_inputs accumulator.
    bounded_int_fraction_interval_valid accumulator /\
    EVERY
      (\object_input.
         bounded_int_fraction_interval_valid (FST object_input) /\
         bounded_int_fraction_interval_valid (SND object_input))
      object_inputs ==>
    bounded_int_fraction_interval_valid
      (bounded_object_q_interval_products_sum_acc_ints
        object_inputs accumulator)
Proof
  Induct
  >> simp
       [bounded_object_q_interval_products_sum_acc_ints_def,
        bounded_object_q_interval_add_ints_valid,
        bounded_object_q_interval_mul_ints_valid]
QED

Theorem bounded_fused_product_inputs_covers_object_q_ints_valid:
  !products object_products.
    LIST_REL bounded_fused_product_input_covers_object_q_ints
      products object_products ==>
    EVERY
      (\object_input.
         bounded_int_fraction_interval_valid (FST object_input) /\
         bounded_int_fraction_interval_valid (SND object_input))
      object_products
Proof
  Induct
  >> Cases_on `object_products`
  >> rw [LIST_REL_def]
  >> Cases_on `h'`
  >> Cases_on `h`
  >> fs [bounded_fused_product_input_covers_object_q_ints_def]
  >> metis_tac [bounded_interval64_covers_object_q_ints_valid]
QED

Theorem bounded_interval64_fused_products_covers_object_q_ints:
  LIST_REL bounded_fused_product_input_covers_object_q_ints
      products object_products /\
  bounded_interval64_fused_products products = SOME result ==>
  bounded_interval64_covers_object_q_ints result
    (bounded_object_q_interval_products_sum_acc_ints
      object_products ((0,1),(0,1)))
Proof
  strip_tac
  >> imp_res_tac
       bounded_fused_product_inputs_covers_object_q_ints_endpoints
  >> `bounded_interval64_contains_int_fraction result
        (bounded_int_fraction_sum_acc
          (MAP bounded_object_q_interval_product_lower_ints object_products)
          (0,1))` by
       metis_tac [bounded_interval64_fused_products_contains_int_fraction]
  >> `bounded_interval64_contains_int_fraction result
        (bounded_int_fraction_sum_acc
          (MAP bounded_object_q_interval_product_upper_ints object_products)
          (0,1))` by
       metis_tac [bounded_interval64_fused_products_contains_int_fraction]
  >> `bounded_int_fraction_interval_valid
        (bounded_object_q_interval_products_sum_acc_ints
          object_products ((0,1),(0,1)))` by
       (irule bounded_object_q_interval_products_sum_acc_ints_valid
        >> simp [bounded_int_fraction_interval_valid_def,
                 bounded_int_fraction_positive_def,
                 bounded_int_fraction_le_def]
        >> metis_tac
             [bounded_fused_product_inputs_covers_object_q_ints_valid])
  >> simp
       [bounded_object_q_interval_products_sum_acc_ints_components]
  >> irule bounded_interval64_contains_fraction_pair_covers
  >> fs
       [bounded_object_q_interval_products_sum_acc_ints_components,
        bounded_int_fraction_interval_valid_def]
QED

Definition bounded_fused_product_input_covers_object_q_def:
  bounded_fused_product_input_covers_object_q
      (left,right) (left_object_interval,right_object_interval) <=>
    bounded_interval64_covers_object_q
      left left_object_interval /\
    bounded_interval64_covers_object_q
      right right_object_interval
End

Definition bounded_object_q_product_input_decodes_def:
  bounded_object_q_product_input_decodes
      (left_object_interval,right_object_interval)
      (left_object_ints,right_object_ints) <=>
    bounded_object_q_interval_ints left_object_interval =
      SOME left_object_ints /\
    bounded_object_q_interval_ints right_object_interval =
      SOME right_object_ints
End

Theorem bounded_fused_product_input_covers_object_q_witness:
  bounded_fused_product_input_covers_object_q input object_input ==>
  ?object_input_ints.
    bounded_fused_product_input_covers_object_q_ints
      input object_input_ints /\
    bounded_object_q_product_input_decodes
      object_input object_input_ints
Proof
  PairCases_on `input`
  >> PairCases_on `object_input`
  >> rw
       [bounded_fused_product_input_covers_object_q_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
  >> every_case_tac
  >> gvs []
  >> qexists_tac `(x',x)`
  >> simp
       [bounded_fused_product_input_covers_object_q_ints_def,
        bounded_object_q_product_input_decodes_def]
QED

Theorem bounded_fused_product_inputs_covers_object_q_witness:
  !products object_products.
    LIST_REL bounded_fused_product_input_covers_object_q
      products object_products ==>
    ?object_product_ints.
      LIST_REL bounded_fused_product_input_covers_object_q_ints
        products object_product_ints /\
      LIST_REL bounded_object_q_product_input_decodes
        object_products object_product_ints
Proof
  Induct
  >> Cases_on `object_products`
  >> simp [LIST_REL_def]
  >> metis_tac [bounded_fused_product_input_covers_object_q_witness]
QED

Definition bounded_object_q_interval_products_sum_acc_cv_def:
  bounded_object_q_interval_products_sum_acc_cv [] accumulator =
      accumulator /\
  bounded_object_q_interval_products_sum_acc_cv
      (object_input::object_inputs) accumulator =
    bounded_object_q_interval_products_sum_acc_cv object_inputs
      (bounded_object_q_interval_add_cv accumulator
        (bounded_object_q_interval_mul_cv
          (FST object_input) (SND object_input)))
End

Theorem bounded_object_q_interval_products_sum_acc_cv_decodes:
  !object_inputs object_input_ints accumulator accumulator_ints.
    LIST_REL bounded_object_q_product_input_decodes
      object_inputs object_input_ints /\
    bounded_object_q_interval_ints accumulator = SOME accumulator_ints ==>
    bounded_object_q_interval_ints
      (bounded_object_q_interval_products_sum_acc_cv
        object_inputs accumulator) =
    SOME
      (bounded_object_q_interval_products_sum_acc_ints
        object_input_ints accumulator_ints)
Proof
  Induct
  >> Cases_on `object_input_ints`
  >> rw
       [LIST_REL_def,
        bounded_object_q_interval_products_sum_acc_cv_def,
        bounded_object_q_interval_products_sum_acc_ints_def]
  >> Cases_on `h'`
  >> Cases_on `h`
  >> fs [bounded_object_q_product_input_decodes_def]
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_mul_cv q r) =
      SOME (bounded_object_q_interval_mul_ints q' r')` by
       (irule bounded_object_q_interval_mul_cv_decodes
        >> simp [])
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_add_cv accumulator
          (bounded_object_q_interval_mul_cv q r)) =
      SOME
        (bounded_object_q_interval_add_ints accumulator_ints
          (bounded_object_q_interval_mul_ints q' r'))` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_decodes
        >> simp [])
  >> qpat_x_assum
       `!object_input_ints accumulator accumulator_ints. _`
       (mp_tac o Q.SPECL
          [`t`,
           `bounded_object_q_interval_add_cv accumulator
              (bounded_object_q_interval_mul_cv q r)`,
           `bounded_object_q_interval_add_ints accumulator_ints
              (bounded_object_q_interval_mul_ints q' r')`])
  >> simp []
QED

Theorem bounded_analytic_source_q_zero_interval_cv_decodes:
  bounded_object_q_interval_ints
      (bounded_analytic_source_q_interval_cv 0 0 0) =
    SOME ((0,1),(0,1))
Proof
  simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
QED

Theorem bounded_interval64_fused_products_covers_object_q:
  LIST_REL bounded_fused_product_input_covers_object_q
      products object_products /\
  bounded_interval64_fused_products products = SOME result ==>
  bounded_interval64_covers_object_q result
    (bounded_object_q_interval_products_sum_acc_cv object_products
      (bounded_analytic_source_q_interval_cv 0 0 0))
Proof
  strip_tac
  >> imp_res_tac
       bounded_fused_product_inputs_covers_object_q_witness
  >> `bounded_object_q_interval_ints
        (bounded_object_q_interval_products_sum_acc_cv object_products
          (bounded_analytic_source_q_interval_cv 0 0 0)) =
      SOME
        (bounded_object_q_interval_products_sum_acc_ints
          object_product_ints ((0,1),(0,1)))` by
       (irule bounded_object_q_interval_products_sum_acc_cv_decodes
        >> simp [bounded_analytic_source_q_zero_interval_cv_decodes])
  >> `bounded_interval64_covers_object_q_ints result
        (bounded_object_q_interval_products_sum_acc_ints
          object_product_ints ((0,1),(0,1)))` by
       metis_tac
         [bounded_interval64_fused_products_covers_object_q_ints]
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def]
QED

Definition bounded_object_q_interval_fused_scale_add_cv_def:
  bounded_object_q_interval_fused_scale_add_cv
      left_scale [] right_scale [] = [] /\
  bounded_object_q_interval_fused_scale_add_cv
      left_scale (left::left_rest) right_scale (right::right_rest) =
    bounded_object_q_interval_products_sum_acc_cv
      [(left_scale,left);(right_scale,right)]
      (bounded_analytic_source_q_interval_cv 0 0 0) ::
    bounded_object_q_interval_fused_scale_add_cv
      left_scale left_rest right_scale right_rest /\
  bounded_object_q_interval_fused_scale_add_cv
      left_scale _ right_scale _ = []
End

Theorem bounded_interval64_fused_scale_add_covers_object_q:
  !left left_object right right_object result.
    bounded_interval64_covers_object_q left_scale left_scale_object /\
    LIST_REL bounded_interval64_covers_object_q left left_object /\
    bounded_interval64_covers_object_q right_scale right_scale_object /\
    LIST_REL bounded_interval64_covers_object_q right right_object /\
    bounded_interval64_fused_scale_add
      left_scale left right_scale right = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_fused_scale_add_cv
        left_scale_object left_object right_scale_object right_object)
Proof
  Induct
  >> Cases_on `left_object`
  >> Cases_on `right`
  >> Cases_on `right_object`
  >> rw
       [compute_boundedTaylorMulTheory.bounded_interval64_fused_scale_add_def,
        bounded_object_q_interval_fused_scale_add_cv_def,
        LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> conj_tac
  >- (irule bounded_interval64_fused_products_covers_object_q
      >> metis_tac
           [LIST_REL_def,
            bounded_fused_product_input_covers_object_q_def])
  >> qpat_x_assum
       `!left_object right right_object result'. _`
       (mp_tac o Q.SPECL [`t`, `t'`, `t''`, `x`])
  >> simp []
QED

Definition bounded_fused_product_pair_covers_object_q_def:
  bounded_fused_product_pair_covers_object_q
      (first,second) (first_object,second_object) <=>
    bounded_fused_product_input_covers_object_q first first_object /\
    bounded_fused_product_input_covers_object_q second second_object
End

Definition bounded_object_q_symmetric_product_pairs_row_cv_def:
  bounded_object_q_symmetric_product_pairs_row_cv
      fixed_left fixed_right [] [] = [] /\
  bounded_object_q_symmetric_product_pairs_row_cv
      fixed_left fixed_right (left::left_rest) (right::right_rest) =
    ((fixed_left,right),(fixed_right,left)) ::
    bounded_object_q_symmetric_product_pairs_row_cv
      fixed_left fixed_right left_rest right_rest /\
  bounded_object_q_symmetric_product_pairs_row_cv
      fixed_left fixed_right _ _ = []
End

Theorem bounded_interval64_symmetric_product_pairs_row_covers_object_q:
  !left left_object right right_object result.
    bounded_interval64_covers_object_q fixed_left fixed_left_object /\
    bounded_interval64_covers_object_q fixed_right fixed_right_object /\
    LIST_REL bounded_interval64_covers_object_q left left_object /\
    LIST_REL bounded_interval64_covers_object_q right right_object /\
    bounded_interval64_symmetric_product_pairs_row
      fixed_left fixed_right left right = SOME result ==>
    LIST_REL bounded_fused_product_pair_covers_object_q result
      (bounded_object_q_symmetric_product_pairs_row_cv
        fixed_left_object fixed_right_object left_object right_object)
Proof
  Induct
  >> Cases_on `left_object`
  >> Cases_on `right`
  >> Cases_on `right_object`
  >> rw
       [compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_row_def,
        bounded_object_q_symmetric_product_pairs_row_cv_def,
        LIST_REL_def]
  >> every_case_tac
  >> gvs
       [LIST_REL_def,
        bounded_fused_product_pair_covers_object_q_def,
        bounded_fused_product_input_covers_object_q_def]
  >> qpat_x_assum
       `!left_object right right_object result'. _`
       (mp_tac o Q.SPECL [`t`, `t'`, `t''`, `x`])
  >> simp []
QED

Definition bounded_object_q_symmetric_product_pairs_cv_def:
  bounded_object_q_symmetric_product_pairs_cv [] [] = [] /\
  bounded_object_q_symmetric_product_pairs_cv
      (left::left_rest) (right::right_rest) =
    bounded_object_q_symmetric_product_pairs_row_cv left right
      (left::left_rest) (right::right_rest) ++
    bounded_object_q_symmetric_product_pairs_cv left_rest right_rest /\
  bounded_object_q_symmetric_product_pairs_cv _ _ = []
End

Theorem bounded_interval64_symmetric_product_pairs_covers_object_q:
  !left left_object right right_object result.
    LIST_REL bounded_interval64_covers_object_q left left_object /\
    LIST_REL bounded_interval64_covers_object_q right right_object /\
    bounded_interval64_symmetric_product_pairs left right = SOME result ==>
    LIST_REL bounded_fused_product_pair_covers_object_q result
      (bounded_object_q_symmetric_product_pairs_cv
        left_object right_object)
Proof
  Induct
  >> Cases_on `left_object`
  >> Cases_on `right`
  >> Cases_on `right_object`
  >> rw
       [compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_def,
        bounded_object_q_symmetric_product_pairs_cv_def,
        LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> `LIST_REL bounded_fused_product_pair_covers_object_q x'
        (bounded_object_q_symmetric_product_pairs_row_cv h h''
          (h::t) (h''::t''))` by
       metis_tac
         [bounded_interval64_symmetric_product_pairs_row_covers_object_q,
          LIST_REL_def]
  >> `LIST_REL bounded_fused_product_pair_covers_object_q x
        (bounded_object_q_symmetric_product_pairs_cv t t'')` by
       (qpat_x_assum
          `!left_object right right_object result. _`
          (mp_tac o Q.SPECL [`t`, `t'`, `t''`, `x`])
        >> simp [])
  >> irule listTheory.LIST_REL_APPEND_suff
  >> simp []
QED

Theorem bounded_fused_product_pair_covers_object_q_components:
  bounded_fused_product_pair_covers_object_q outer object_outer ==>
  bounded_fused_product_input_covers_object_q
    (FST outer) (FST object_outer) /\
  bounded_fused_product_input_covers_object_q
    (SND outer) (SND object_outer)
Proof
  PairCases_on `outer`
  >> PairCases_on `object_outer`
  >> simp [bounded_fused_product_pair_covers_object_q_def]
QED

Definition bounded_object_q_interval_fused_hessian_cv_def:
  bounded_object_q_interval_fused_hessian_cv
      left_value right_value [] [] [] = [] /\
  bounded_object_q_interval_fused_hessian_cv left_value right_value
      (left_hessian::left_rest) (right_hessian::right_rest)
      (outer::outer_rest) =
    bounded_object_q_interval_products_sum_acc_cv
      [(right_value,left_hessian);FST outer;SND outer;
       (left_value,right_hessian)]
      (bounded_analytic_source_q_interval_cv 0 0 0) ::
    bounded_object_q_interval_fused_hessian_cv left_value right_value
      left_rest right_rest outer_rest /\
  bounded_object_q_interval_fused_hessian_cv
      left_value right_value _ _ _ = []
End

Theorem bounded_interval64_fused_hessian_covers_object_q:
  !left_hessian left_object_hessian
    right_hessian right_object_hessian outer object_outer result.
    bounded_interval64_covers_object_q left_value left_object_value /\
    bounded_interval64_covers_object_q right_value right_object_value /\
    LIST_REL bounded_interval64_covers_object_q
      left_hessian left_object_hessian /\
    LIST_REL bounded_interval64_covers_object_q
      right_hessian right_object_hessian /\
    LIST_REL bounded_fused_product_pair_covers_object_q
      outer object_outer /\
    bounded_interval64_fused_hessian left_value right_value
      left_hessian right_hessian outer = SOME result ==>
    LIST_REL bounded_interval64_covers_object_q result
      (bounded_object_q_interval_fused_hessian_cv
        left_object_value right_object_value
        left_object_hessian right_object_hessian object_outer)
Proof
  Induct
  >> Cases_on `left_object_hessian`
  >> Cases_on `right_hessian`
  >> Cases_on `right_object_hessian`
  >> Cases_on `outer`
  >> Cases_on `object_outer`
  >> rw
       [compute_boundedTaylorMulTheory.bounded_interval64_fused_hessian_def,
        bounded_object_q_interval_fused_hessian_cv_def,
        LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> imp_res_tac bounded_fused_product_pair_covers_object_q_components
  >> conj_tac
  >- (irule bounded_interval64_fused_products_covers_object_q
      >> metis_tac
           [LIST_REL_def,
            bounded_fused_product_input_covers_object_q_def])
  >> qpat_x_assum
       `!left_object_hessian right_hessian right_object_hessian outer
          object_outer result'. _`
       (mp_tac o Q.SPECL
          [`t`, `t'`, `t''`, `t'³'`, `t'⁴'`, `x`])
  >> simp []
QED

Definition bounded_taylor64_complete_inputs_cover_object_q_def:
  bounded_taylor64_complete_inputs_cover_object_q
      domain center_value center_gradient hessian
      object_domain object_center_value object_center_gradient
      object_hessian <=>
    domain = object_domain /\
    bounded_interval64_covers_object_q
      center_value object_center_value /\
    LIST_REL bounded_interval64_covers_object_q
      center_gradient object_center_gradient /\
    LIST_REL bounded_interval64_covers_object_q
      hessian object_hessian
End

Theorem bounded_taylor64_mul_reaches_object_q_complete_inputs:
  bounded_taylor64_covers_object_q_state left left_object_domain
      left_object_center_value left_object_center_gradient
      left_object_value_bound left_object_gradient_bounds
      left_object_hessian /\
  bounded_taylor64_covers_object_q_state right right_object_domain
      right_object_center_value right_object_center_gradient
      right_object_value_bound right_object_gradient_bounds
      right_object_hessian /\
  bounded_taylor64_mul radii left right = SOME result ==>
  ?center_value center_gradient hessian.
    bounded_taylor64_complete radii
      (left_object_domain /\ right_object_domain)
      center_value center_gradient hessian = SOME result /\
    bounded_taylor64_complete_inputs_cover_object_q
      (left_object_domain /\ right_object_domain)
      center_value center_gradient hessian
      (left_object_domain /\ right_object_domain)
      (bounded_object_q_interval_mul_cv
        left_object_center_value right_object_center_value)
      (bounded_object_q_interval_fused_scale_add_cv
        right_object_center_value left_object_center_gradient
        left_object_center_value right_object_center_gradient)
      (bounded_object_q_interval_fused_hessian_cv
        left_object_value_bound right_object_value_bound
        left_object_hessian right_object_hessian
        (bounded_object_q_symmetric_product_pairs_cv
          left_object_gradient_bounds right_object_gradient_bounds))
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def,
        compute_boundedTaylorMulTheory.bounded_taylor64_mul_def]
  >> every_case_tac
  >> gvs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> `bounded_interval64_covers_object_q x'³'
        (bounded_object_q_interval_mul_cv
          left_object_center_value right_object_center_value)` by
       metis_tac [bounded_interval64_mul_covers_object_q]
  >> `LIST_REL bounded_interval64_covers_object_q x''
        (bounded_object_q_interval_fused_scale_add_cv
          right_object_center_value left_object_center_gradient
          left_object_center_value right_object_center_gradient)` by
       metis_tac [bounded_interval64_fused_scale_add_covers_object_q]
  >> `LIST_REL bounded_fused_product_pair_covers_object_q x
        (bounded_object_q_symmetric_product_pairs_cv
          left_object_gradient_bounds right_object_gradient_bounds)` by
       metis_tac
         [bounded_interval64_symmetric_product_pairs_covers_object_q]
  >> `LIST_REL bounded_interval64_covers_object_q x'
        (bounded_object_q_interval_fused_hessian_cv
          left_object_value_bound right_object_value_bound
          left_object_hessian right_object_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            left_object_gradient_bounds right_object_gradient_bounds))` by
       metis_tac [bounded_interval64_fused_hessian_covers_object_q]
  >> qexists_tac `x'³'`
  >> qexists_tac `x''`
  >> qexists_tac `x'`
  >> simp [bounded_taylor64_complete_inputs_cover_object_q_def]
QED

val _ = export_theory ();
