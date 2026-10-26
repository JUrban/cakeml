(*****************************************************************************
 * Exact object-q witnesses for the generic scale-2^40 interval product.
 *
 * Products deliberately remain unnormalised.  The endpoint selector compares
 * signed rationals by positive-denominator cross multiplication, matching the
 * four-corner interval product independently of any later GCD normalization.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectProductRefinement
Ancestors
  compute_boundedAnalyticObjectLinearRefinement
Libs
  bossLib preamble intLib

Definition bounded_object_q_mul_cv_def:
  bounded_object_q_mul_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) =
    Pair
      (Pair
        (Num
          (left_positive * right_positive +
           left_negative * right_negative))
        (Num
          (left_positive * right_negative +
           left_negative * right_positive)))
      (Num
        (SUC left_denominator_minus_one *
           SUC right_denominator_minus_one - 1)) /\
  bounded_object_q_mul_cv _ _ = Num 0
End

Definition bounded_int_fraction_mul_def:
  bounded_int_fraction_mul
      ((left_numerator,left_denominator):int # int)
      ((right_numerator,right_denominator):int # int) =
    (left_numerator * right_numerator,
     left_denominator * right_denominator)
End

Definition bounded_int_fraction_le_def:
  bounded_int_fraction_le
      ((left_numerator,left_denominator):int # int)
      ((right_numerator,right_denominator):int # int) <=>
    left_numerator * right_denominator <=
      right_numerator * left_denominator
End

Definition bounded_int_fraction_min_def:
  bounded_int_fraction_min left right =
    if bounded_int_fraction_le left right then left else right
End

Definition bounded_int_fraction_max_def:
  bounded_int_fraction_max left right =
    if bounded_int_fraction_le left right then right else left
End

Definition bounded_int_fraction_min4_def:
  bounded_int_fraction_min4 first second third fourth =
    bounded_int_fraction_min
      (bounded_int_fraction_min first second)
      (bounded_int_fraction_min third fourth)
End

Definition bounded_int_fraction_max4_def:
  bounded_int_fraction_max4 first second third fourth =
    bounded_int_fraction_max
      (bounded_int_fraction_max first second)
      (bounded_int_fraction_max third fourth)
End

Definition bounded_object_q_le_cv_def:
  bounded_object_q_le_cv
      (Pair (Pair (Num left_positive) (Num left_negative))
        (Num left_denominator_minus_one))
      (Pair (Pair (Num right_positive) (Num right_negative))
        (Num right_denominator_minus_one)) =
    (left_positive * SUC right_denominator_minus_one +
        right_negative * SUC left_denominator_minus_one <=
      right_positive * SUC left_denominator_minus_one +
        left_negative * SUC right_denominator_minus_one) /\
  bounded_object_q_le_cv _ _ = F
End

Definition bounded_object_q_min_cv_def:
  bounded_object_q_min_cv left right =
    if bounded_object_q_le_cv left right then left else right
End

Definition bounded_object_q_max_cv_def:
  bounded_object_q_max_cv left right =
    if bounded_object_q_le_cv left right then right else left
End

Definition bounded_object_q_min4_cv_def:
  bounded_object_q_min4_cv first second third fourth =
    bounded_object_q_min_cv
      (bounded_object_q_min_cv first second)
      (bounded_object_q_min_cv third fourth)
End

Definition bounded_object_q_max4_cv_def:
  bounded_object_q_max4_cv first second third fourth =
    bounded_object_q_max_cv
      (bounded_object_q_max_cv first second)
      (bounded_object_q_max_cv third fourth)
End

Definition bounded_object_q_interval_mul_cv_def:
  bounded_object_q_interval_mul_cv
      (Pair left_lower left_upper) (Pair right_lower right_upper) =
    (let lower_lower = bounded_object_q_mul_cv left_lower right_lower;
        lower_upper = bounded_object_q_mul_cv left_lower right_upper;
        upper_lower = bounded_object_q_mul_cv left_upper right_lower;
        upper_upper = bounded_object_q_mul_cv left_upper right_upper
    in
      Pair
        (bounded_object_q_min4_cv
          lower_lower lower_upper upper_lower upper_upper)
        (bounded_object_q_max4_cv
          lower_lower lower_upper upper_lower upper_upper)) /\
  bounded_object_q_interval_mul_cv _ _ = Num 0
End

Definition bounded_object_q_interval_mul_ints_def:
  bounded_object_q_interval_mul_ints
      ((left_lower,left_upper):(int # int) # (int # int))
      ((right_lower,right_upper):(int # int) # (int # int)) =
    let lower_lower = bounded_int_fraction_mul left_lower right_lower;
        lower_upper = bounded_int_fraction_mul left_lower right_upper;
        upper_lower = bounded_int_fraction_mul left_upper right_lower;
        upper_upper = bounded_int_fraction_mul left_upper right_upper
    in
      (bounded_int_fraction_min4
        lower_lower lower_upper upper_lower upper_upper,
       bounded_int_fraction_max4
        lower_lower lower_upper upper_lower upper_upper)
End

Theorem bounded_object_q_mul_cv_decodes:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  bounded_object_q_ints (bounded_object_q_mul_cv left right) =
    SOME (bounded_int_fraction_mul left_fraction right_fraction)
Proof
  PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> `SUC
        (SUC denominator_minus_one' * SUC denominator_minus_one - 1) =
      SUC denominator_minus_one' * SUC denominator_minus_one` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> simp [])
  >> simp
       [bounded_object_q_mul_cv_def, bounded_int_fraction_mul_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_MUL]
  >> conj_tac
  >- (REWRITE_TAC
        [GSYM integerTheory.INT_ADD, GSYM integerTheory.INT_MUL]
      >> INT_RING_TAC)
  >> metis_tac [arithmeticTheory.MULT_COMM]
QED

Theorem bounded_object_q_le_cv_correct:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  (bounded_object_q_le_cv left right <=>
   bounded_int_fraction_le left_fraction right_fraction)
Proof
  PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> strip_tac
  >> imp_res_tac
       compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_ints_components
  >> gvs []
  >> simp
       [bounded_object_q_le_cv_def, bounded_int_fraction_le_def,
        GSYM integerTheory.INT_ADD, GSYM integerTheory.INT_MUL]
  >> REWRITE_TAC
       [GSYM integerTheory.INT_LE, GSYM integerTheory.INT_ADD,
        GSYM integerTheory.INT_MUL]
  >> simp [integerTheory.INT_SUB_RDISTRIB]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_q_min_cv_decodes:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  bounded_object_q_ints (bounded_object_q_min_cv left right) =
    SOME (bounded_int_fraction_min left_fraction right_fraction)
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_le_cv_correct
  >> rw [bounded_object_q_min_cv_def, bounded_int_fraction_min_def]
QED

Theorem bounded_object_q_max_cv_decodes:
  bounded_object_q_ints left = SOME left_fraction /\
  bounded_object_q_ints right = SOME right_fraction ==>
  bounded_object_q_ints (bounded_object_q_max_cv left right) =
    SOME (bounded_int_fraction_max left_fraction right_fraction)
Proof
  strip_tac
  >> imp_res_tac bounded_object_q_le_cv_correct
  >> rw [bounded_object_q_max_cv_def, bounded_int_fraction_max_def]
QED

Theorem bounded_object_q_min4_cv_decodes:
  bounded_object_q_ints q1 = SOME fraction1 /\
  bounded_object_q_ints q2 = SOME fraction2 /\
  bounded_object_q_ints q3 = SOME fraction3 /\
  bounded_object_q_ints q4 = SOME fraction4 ==>
  bounded_object_q_ints
      (bounded_object_q_min4_cv q1 q2 q3 q4) =
    SOME
      (bounded_int_fraction_min4 fraction1 fraction2 fraction3 fraction4)
Proof
  strip_tac
  >> `bounded_object_q_ints (bounded_object_q_min_cv q1 q2) =
        SOME (bounded_int_fraction_min fraction1 fraction2)` by
       (irule bounded_object_q_min_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_min_cv q3 q4) =
        SOME (bounded_int_fraction_min fraction3 fraction4)` by
       (irule bounded_object_q_min_cv_decodes >> simp [])
  >> fs [bounded_object_q_min4_cv_def, bounded_int_fraction_min4_def]
  >> irule bounded_object_q_min_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_max4_cv_decodes:
  bounded_object_q_ints q1 = SOME fraction1 /\
  bounded_object_q_ints q2 = SOME fraction2 /\
  bounded_object_q_ints q3 = SOME fraction3 /\
  bounded_object_q_ints q4 = SOME fraction4 ==>
  bounded_object_q_ints
      (bounded_object_q_max4_cv q1 q2 q3 q4) =
    SOME
      (bounded_int_fraction_max4 fraction1 fraction2 fraction3 fraction4)
Proof
  strip_tac
  >> `bounded_object_q_ints (bounded_object_q_max_cv q1 q2) =
        SOME (bounded_int_fraction_max fraction1 fraction2)` by
       (irule bounded_object_q_max_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_max_cv q3 q4) =
        SOME (bounded_int_fraction_max fraction3 fraction4)` by
       (irule bounded_object_q_max_cv_decodes >> simp [])
  >> fs [bounded_object_q_max4_cv_def, bounded_int_fraction_max4_def]
  >> irule bounded_object_q_max_cv_decodes
  >> simp []
QED

Theorem bounded_object_q_interval_mul_cv_decodes:
  bounded_object_q_interval_ints left = SOME left_object_interval /\
  bounded_object_q_interval_ints right = SOME right_object_interval ==>
  bounded_object_q_interval_ints
      (bounded_object_q_interval_mul_cv left right) =
    SOME
      (bounded_object_q_interval_mul_ints
        left_object_interval right_object_interval)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [bounded_object_q_interval_mul_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> every_case_tac
  >> gvs
       [bounded_object_q_interval_mul_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c c') =
        SOME (bounded_int_fraction_mul lower' lower'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c c0') =
        SOME (bounded_int_fraction_mul lower' upper'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0 c') =
        SOME (bounded_int_fraction_mul upper' lower'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints (bounded_object_q_mul_cv c0 c0') =
        SOME (bounded_int_fraction_mul upper' upper'')` by
       (irule bounded_object_q_mul_cv_decodes >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_min4_cv
          (bounded_object_q_mul_cv c c')
          (bounded_object_q_mul_cv c c0')
          (bounded_object_q_mul_cv c0 c')
          (bounded_object_q_mul_cv c0 c0')) =
        SOME
          (bounded_int_fraction_min4
            (bounded_int_fraction_mul lower' lower'')
            (bounded_int_fraction_mul lower' upper'')
            (bounded_int_fraction_mul upper' lower'')
            (bounded_int_fraction_mul upper' upper''))` by
       (irule bounded_object_q_min4_cv_decodes >> simp [])
  >> `bounded_object_q_ints
        (bounded_object_q_max4_cv
          (bounded_object_q_mul_cv c c')
          (bounded_object_q_mul_cv c c0')
          (bounded_object_q_mul_cv c0 c')
          (bounded_object_q_mul_cv c0 c0')) =
        SOME
          (bounded_int_fraction_max4
            (bounded_int_fraction_mul lower' lower'')
            (bounded_int_fraction_mul lower' upper'')
            (bounded_int_fraction_mul upper' lower'')
            (bounded_int_fraction_mul upper' upper''))` by
       (irule bounded_object_q_max4_cv_decodes >> simp [])
  >> gvs [bounded_object_q_interval_mul_ints_def]
QED

Definition bounded_interval64_contains_int_fraction_def:
  bounded_interval64_contains_int_fraction interval
      ((numerator,denominator):int # int) <=>
    0 < denominator /\
    denominator *
        bounded_signed64_to_int (bounded_interval64_lower interval) <=
      (&1099511627776:int) * numerator /\
    (&1099511627776:int) * numerator <=
      denominator *
        bounded_signed64_to_int (bounded_interval64_upper interval)
End

Theorem bounded_int_positive_scales_product_corner:
  0 < (left_scale:int) /\ 0 < right_scale /\
  (&1099511627776:int) * output_lower <= left * right /\
  left * right <= (&1099511627776:int) * output_upper ==>
  (&1099511627776:int) * left_scale * right_scale * output_lower <=
      (left_scale * left) * (right_scale * right) /\
  (left_scale * left) * (right_scale * right) <=
      (&1099511627776:int) * left_scale * right_scale * output_upper
Proof
  strip_tac
  >> `0 <= left_scale * right_scale` by
       (irule integerTheory.INT_LE_MUL >> intLib.ARITH_TAC)
  >> `(left_scale * right_scale) *
        ((&1099511627776:int) * output_lower) <=
      (left_scale * right_scale) * (left * right)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> `(left_scale * right_scale) * (left * right) <=
      (left_scale * right_scale) *
        ((&1099511627776:int) * output_upper)` by
       (irule
          compute_boundedIntervalTheory.bounded_int_mul_left_mono_nonnegative
        >> simp [])
  >> `(&1099511627776:int) * left_scale * right_scale * output_lower =
      (left_scale * right_scale) *
        ((&1099511627776:int) * output_lower)` by INT_RING_TAC
  >> `(left_scale * left) * (right_scale * right) =
      (left_scale * right_scale) * (left * right)` by INT_RING_TAC
  >> `(&1099511627776:int) * left_scale * right_scale * output_upper =
      (left_scale * right_scale) *
        ((&1099511627776:int) * output_upper)` by INT_RING_TAC
  >> metis_tac []
QED

Theorem bounded_scale40_cancel_fraction_product:
  0 < (left_denominator:int) /\ 0 < right_denominator /\
  (&1099511627776:int) * left_denominator * right_denominator *
      output_lower <=
    ((&1099511627776:int) * left_numerator) *
      ((&1099511627776:int) * right_numerator) /\
  ((&1099511627776:int) * left_numerator) *
      ((&1099511627776:int) * right_numerator) <=
    (&1099511627776:int) * left_denominator * right_denominator *
      output_upper ==>
  0 < left_denominator * right_denominator /\
  left_denominator * right_denominator * output_lower <=
    (&1099511627776:int) * (left_numerator * right_numerator) /\
  (&1099511627776:int) * (left_numerator * right_numerator) <=
    left_denominator * right_denominator * output_upper
Proof
  strip_tac
  >> conj_tac >- simp [integerTheory.INT_MUL_SIGN_CASES]
  >> `(&1099511627776:int) * left_denominator * right_denominator *
        output_lower =
      (&1099511627776:int) *
        (left_denominator * right_denominator * output_lower)` by
       INT_RING_TAC
  >> `((&1099511627776:int) * left_numerator) *
        ((&1099511627776:int) * right_numerator) =
      (&1099511627776:int) *
        ((&1099511627776:int) *
          (left_numerator * right_numerator))` by INT_RING_TAC
  >> `(&1099511627776:int) * left_denominator * right_denominator *
        output_upper =
      (&1099511627776:int) *
        (left_denominator * right_denominator * output_upper)` by
       INT_RING_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_mul_contains_int_fraction_product:
  bounded_interval64_contains_int_fraction left left_fraction /\
  bounded_interval64_contains_int_fraction right right_fraction /\
  bounded_interval64_mul left right = SOME result ==>
  bounded_interval64_contains_int_fraction result
    (bounded_int_fraction_mul left_fraction right_fraction)
Proof
  PairCases_on `left_fraction`
  >> PairCases_on `right_fraction`
  >> Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rename1
       `bounded_interval64_mul
          (BoundedInterval64 left_lower left_upper)
          (BoundedInterval64 right_lower right_upper) =
        SOME (BoundedInterval64 output_lower output_upper)`
  >> strip_tac
  >> `bounded_interval64_valid
        (BoundedInterval64 left_lower left_upper) /\
      bounded_interval64_valid
        (BoundedInterval64 right_lower right_upper)` by
       fs [compute_boundedIntervalTheory.bounded_interval64_mul_def]
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
  >> `(&1099511627776:int) * bounded_signed64_to_int output_lower <=
        bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower /\
      bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower <=
        (&1099511627776:int) * bounded_signed64_to_int output_upper` by
       metis_tac
         [compute_boundedIntervalTheory.bounded_interval64_mul_contains_product]
  >> `(&1099511627776:int) * bounded_signed64_to_int output_lower <=
        bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper /\
      bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper <=
        (&1099511627776:int) * bounded_signed64_to_int output_upper` by
       metis_tac
         [compute_boundedIntervalTheory.bounded_interval64_mul_contains_product]
  >> `(&1099511627776:int) * bounded_signed64_to_int output_lower <=
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower /\
      bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower <=
        (&1099511627776:int) * bounded_signed64_to_int output_upper` by
       metis_tac
         [compute_boundedIntervalTheory.bounded_interval64_mul_contains_product]
  >> `(&1099511627776:int) * bounded_signed64_to_int output_lower <=
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper /\
      bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper <=
        (&1099511627776:int) * bounded_signed64_to_int output_upper` by
       metis_tac
         [compute_boundedIntervalTheory.bounded_interval64_mul_contains_product]
  >> `0 < left_fraction1 /\ 0 < right_fraction1` by
       fs [bounded_interval64_contains_int_fraction_def]
  >> `(&1099511627776:int) * left_fraction1 * right_fraction1 *
        bounded_signed64_to_int output_lower <=
        (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_lower) /\
      (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_lower) <=
        (&1099511627776:int) * left_fraction1 * right_fraction1 *
          bounded_signed64_to_int output_upper` by
       metis_tac [bounded_int_positive_scales_product_corner]
  >> `(&1099511627776:int) * left_fraction1 * right_fraction1 *
        bounded_signed64_to_int output_lower <=
        (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_upper) /\
      (left_fraction1 * bounded_signed64_to_int left_lower) *
          (right_fraction1 * bounded_signed64_to_int right_upper) <=
        (&1099511627776:int) * left_fraction1 * right_fraction1 *
          bounded_signed64_to_int output_upper` by
       metis_tac [bounded_int_positive_scales_product_corner]
  >> `(&1099511627776:int) * left_fraction1 * right_fraction1 *
        bounded_signed64_to_int output_lower <=
        (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_lower) /\
      (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_lower) <=
        (&1099511627776:int) * left_fraction1 * right_fraction1 *
          bounded_signed64_to_int output_upper` by
       metis_tac [bounded_int_positive_scales_product_corner]
  >> `(&1099511627776:int) * left_fraction1 * right_fraction1 *
        bounded_signed64_to_int output_lower <=
        (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_upper) /\
      (left_fraction1 * bounded_signed64_to_int left_upper) *
          (right_fraction1 * bounded_signed64_to_int right_upper) <=
        (&1099511627776:int) * left_fraction1 * right_fraction1 *
          bounded_signed64_to_int output_upper` by
       metis_tac [bounded_int_positive_scales_product_corner]
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
  >> fs [bounded_interval64_contains_int_fraction_def]
  >> disch_then assume_tac
  >> mp_tac
       (Q.INST
         [`lower` |->
            `(&1099511627776:int) * left_fraction1 * right_fraction1 *
               bounded_signed64_to_int output_lower`,
          `corner1` |->
            `(left_fraction1 * bounded_signed64_to_int left_lower) *
               (right_fraction1 * bounded_signed64_to_int right_lower)`,
          `corner2` |->
            `(left_fraction1 * bounded_signed64_to_int left_lower) *
               (right_fraction1 * bounded_signed64_to_int right_upper)`,
          `corner3` |->
            `(left_fraction1 * bounded_signed64_to_int left_upper) *
               (right_fraction1 * bounded_signed64_to_int right_lower)`,
          `corner4` |->
            `(left_fraction1 * bounded_signed64_to_int left_upper) *
               (right_fraction1 * bounded_signed64_to_int right_upper)`,
          `value` |->
            `((&1099511627776:int) * left_fraction0) *
               ((&1099511627776:int) * right_fraction0)`,
          `upper` |->
            `(&1099511627776:int) * left_fraction1 * right_fraction1 *
               bounded_signed64_to_int output_upper`]
         compute_boundedIntervalTheory.bounded_int_four_corners_enclose)
  >> simp []
  >> disch_then strip_assume_tac
  >> fs [bounded_interval64_contains_int_fraction_def,
         bounded_int_fraction_mul_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> irule bounded_scale40_cancel_fraction_product
  >> conj_tac >> metis_tac []
QED

val _ = export_theory ();
