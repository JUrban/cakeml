(*****************************************************************************
 * Exact fused-product refinement for the authenticated decimal object
 * checker.  The first layer below proves that the sign-selected fixed-word
 * raw bounds are exactly the same four-corner extrema as the object's raw
 * interval product.  Subsequent layers can therefore accumulate products
 * and apply the single outward decimal rounding at the same boundary.
 *****************************************************************************)
Theory compute_boundedObjectDecimalFused
Ancestors
  compute_boundedObjectDecimalAdd compute_boundedObjectDecimalInterval
  compute_boundedTaylorFusedDecimal
Libs
  bossLib preamble intLib

Theorem bounded_interval64_raw_mul_bounds_are_corner_members:
  let bounds = bounded_interval64_raw_mul_bounds_unchecked
    (BoundedInterval64 left_lower left_upper)
    (BoundedInterval64 right_lower right_upper);
      lower = bounded_signed128_to_int (FST bounds);
      upper = bounded_signed128_to_int (SND bounds);
      lower_lower = bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower;
      lower_upper = bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper;
      upper_lower = bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower;
      upper_upper = bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper
  in
    (lower = lower_lower \/ lower = lower_upper \/
     lower = upper_lower \/ lower = upper_upper) /\
    (upper = lower_lower \/ upper = lower_upper \/
     upper = upper_lower \/ upper = upper_upper)
Proof
  Cases_on `bounded_signed64_nonnegative left_lower`
  >> Cases_on `bounded_signed64_nonpositive left_upper`
  >> Cases_on `bounded_signed64_nonnegative right_lower`
  >> Cases_on `bounded_signed64_nonpositive right_upper`
  >> simp
       [compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_unchecked_def,
        compute_boundedTaylorMulTheory.bounded_interval64_raw_product_from_pairs_def,
        compute_boundedTaylorMulTheory.bounded_interval64_raw_product_mixed_def,
        compute_boundedTaylorMulTheory.bounded_signed128_min_value,
        compute_boundedTaylorMulTheory.bounded_signed128_max_value,
        compute_boundedTaylorMulTheory.bounded_signed64_raw_product_value,
        LET_THM]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_interval64_raw_mul_bounds_object_extrema:
  bounded_interval64_valid
      (BoundedInterval64 left_lower left_upper) /\
  bounded_interval64_valid
      (BoundedInterval64 right_lower right_upper) ==>
  let bounds = bounded_interval64_raw_mul_bounds_unchecked
    (BoundedInterval64 left_lower left_upper)
    (BoundedInterval64 right_lower right_upper) in
  bounded_signed128_to_int (FST bounds) =
    bounded_object_int_min4
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper) /\
  bounded_signed128_to_int (SND bounds) =
    bounded_object_int_max4
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper)
Proof
  strip_tac
  >> mp_tac
       (INST
         [``(left_lower:int)`` |->
            ``bounded_signed64_to_int (left_lower:bounded_signed64)``,
          ``(left_upper:int)`` |->
            ``bounded_signed64_to_int (left_upper:bounded_signed64)``,
          ``(right_lower:int)`` |->
            ``bounded_signed64_to_int (right_lower:bounded_signed64)``,
          ``(right_upper:int)`` |->
            ``bounded_signed64_to_int (right_upper:bounded_signed64)``,
          ``(lower:int)`` |->
            ``bounded_signed128_to_int
                (FST (bounded_interval64_raw_mul_bounds_unchecked
                  (BoundedInterval64 left_lower left_upper)
                  (BoundedInterval64 right_lower right_upper)))``,
          ``(upper:int)`` |->
            ``bounded_signed128_to_int
                (SND (bounded_interval64_raw_mul_bounds_unchecked
                  (BoundedInterval64 left_lower left_upper)
                  (BoundedInterval64 right_lower right_upper)))``]
         bounded_object_int_product_extrema_from_bounds)
  >> impl_tac
  >- (fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
      >> conj_tac
      >- (mp_tac
           (Q.INST
             [`left_lower` |-> `left_lower`,
              `left_upper` |-> `left_upper`,
              `right_lower` |-> `right_lower`,
             `right_upper` |-> `right_upper`]
             bounded_interval64_raw_mul_bounds_are_corner_members)
          >> simp [LET_THM])
      >> conj_tac
      >- (mp_tac
           (Q.INST
             [`left_lower` |-> `left_lower`,
              `left_upper` |-> `left_upper`,
              `right_lower` |-> `right_lower`,
              `right_upper` |-> `right_upper`]
             bounded_interval64_raw_mul_bounds_are_corner_members)
          >> simp [LET_THM])
      >> rpt gen_tac
      >> strip_tac
      >> mp_tac
           (Q.INST
             [`left` |-> `BoundedInterval64 left_lower left_upper`,
              `right` |-> `BoundedInterval64 right_lower right_upper`,
              `left_value` |-> `left_value`,
              `right_value` |-> `right_value`]
             compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_contains_product)
      >> simp
           [compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
            compute_boundedIntervalTheory.bounded_interval64_lower_def,
            compute_boundedIntervalTheory.bounded_interval64_upper_def,
            compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            LET_THM])
  >> simp [LET_THM]
QED

Theorem bounded_interval64_raw_mul_bounds_object_values:
  bounded_interval64_valid left /\
  bounded_interval64_valid right ==>
  ?object_lower object_upper.
    bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) =
        SOME (Pair object_lower object_upper) /\
    let bounds = bounded_interval64_raw_mul_bounds_unchecked left right in
    bounded_object_signed_int object_lower =
      SOME (bounded_signed128_to_int (FST bounds)) /\
    bounded_object_signed_int object_upper =
      SOME (bounded_signed128_to_int (SND bounds))
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `b`, `left_upper` |-> `b0`,
          `right_lower` |-> `b'`, `right_upper` |-> `b0'`]
         bounded_object_fs_raw_interval_mul_object_cv_exists)
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` assume_tac))
  >> qexists_tac `object_lower`
  >> qexists_tac `object_upper`
  >> conj_tac
  >- simp []
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `b`, `left_upper` |-> `b0`,
          `right_lower` |-> `b'`, `right_upper` |-> `b0'`,
          `lower` |-> `object_lower`, `upper` |-> `object_upper`]
         bounded_object_fs_raw_interval_mul_signed_values)
  >> impl_tac
  >- fs
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `b`, `left_upper` |-> `b0`,
          `right_lower` |-> `b'`, `right_upper` |-> `b0'`]
         bounded_interval64_raw_mul_bounds_object_extrema)
  >> simp [LET_THM]
QED

Definition bounded_object_fs_raw_products_acc_def:
  bounded_object_fs_raw_products_acc [] accumulator = SOME accumulator /\
  bounded_object_fs_raw_products_acc ((left,right)::products) accumulator =
    (case bounded_object_fs_raw_interval_mul
       (bounded_interval64_object_cv left)
       (bounded_interval64_object_cv right) of
     | NONE => NONE
     | SOME raw_product =>
       case bounded_object_fs_raw_interval_add accumulator raw_product of
       | NONE => NONE
       | SOME next => bounded_object_fs_raw_products_acc products next)
End

Definition bounded_signed192_object_cv_def:
  bounded_signed192_object_cv
      (BoundedSigned192 negative magnitude) : cv =
    if negative then Pair (Num 0) (Num (bounded192_to_num magnitude))
    else Pair (Num (bounded192_to_num magnitude)) (Num 0)
End

Theorem bounded_object_signed_int_signed192_object_cv[simp]:
  bounded_object_signed_int (bounded_signed192_object_cv value) =
    SOME (bounded_signed192_to_int value)
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> simp
       [bounded_signed192_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedWideSignedTheory.bounded_signed192_to_int_def]
QED

Theorem bounded_signed192_floor64_decimal_object_exact:
  bounded_signed192_floor64_decimal source = SOME result ==>
  bounded_object_fs_floor_div
      (bounded_signed192_object_cv source) 1000000000000 =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `source`
  >> Cases_on `b`
  >> rw
       [compute_boundedTaylorFusedDecimalTheory.bounded_signed192_floor64_decimal_def]
  >> every_case_tac
  >> gvs
       [bounded_signed192_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_decimal,
        compute_boundedTaylorFusedDecimalTheory.bounded192_floor64_decimal_def,
        compute_boundedTaylorFusedDecimalTheory.bounded192_ceil64_decimal_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        LET_THM]
  >> fs [compute_boundedTheory.bounded_word_base_eq, LESS_MOD,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> Cases_on `bounded192_to_num b0 = 0`
  >> simp [arithmeticTheory.DIV_EQ_0]
QED

Theorem bounded_signed192_ceil64_decimal_object_exact:
  bounded_signed192_ceil64_decimal source = SOME result ==>
  bounded_object_fs_ceil_div
      (bounded_signed192_object_cv source) 1000000000000 =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `source`
  >> Cases_on `b`
  >> rw
       [compute_boundedTaylorFusedDecimalTheory.bounded_signed192_ceil64_decimal_def]
  >> every_case_tac
  >> gvs
       [bounded_signed192_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_decimal,
        compute_boundedTaylorFusedDecimalTheory.bounded192_floor64_decimal_def,
        compute_boundedTaylorFusedDecimalTheory.bounded192_ceil64_decimal_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        LET_THM]
  >> fs [compute_boundedTheory.bounded_word_base_eq, LESS_MOD,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> Cases_on `bounded192_to_num b0 = 0`
  >> Cases_on `bounded192_to_num b0 DIV 1000000000000 = 0`
  >> simp []
QED

Theorem bounded_object_fs_raw_interval_round_signed192_exact:
  bounded_object_signed_int object_lower =
      SOME (bounded_signed192_to_int word_lower) /\
  bounded_object_signed_int object_upper =
      SOME (bounded_signed192_to_int word_upper) /\
  bounded_signed192_floor64_decimal word_lower = SOME result_lower /\
  bounded_signed192_ceil64_decimal word_upper = SOME result_upper ==>
  bounded_object_fs_raw_interval_round 1000000000000
      (Pair object_lower object_upper) =
    SOME
      (bounded_interval64_object_cv
        (BoundedInterval64 result_lower result_upper))
Proof
  strip_tac
  >> `bounded_object_fs_raw_interval_round 1000000000000
        (Pair object_lower object_upper) =
      bounded_object_fs_raw_interval_round 1000000000000
        (Pair (bounded_signed192_object_cv word_lower)
          (bounded_signed192_object_cv word_upper))` by
       (irule
          compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_extensional
        >> simp [])
  >> pop_assum SUBST1_TAC
  >> irule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_exact
  >> simp [bounded_signed192_floor64_decimal_object_exact,
           bounded_signed192_ceil64_decimal_object_exact]
QED

Theorem bounded_object_fs_raw_products_acc_refines:
  !products word_lower word_upper object_lower object_upper result.
    bounded_object_signed_int object_lower =
        SOME (bounded_signed192_to_int word_lower) /\
    bounded_object_signed_int object_upper =
        SOME (bounded_signed192_to_int word_upper) /\
    bounded_interval64_raw_sum_acc products word_lower word_upper =
        SOME result ==>
    ?result_lower result_upper.
      bounded_object_fs_raw_products_acc products
        (Pair object_lower object_upper) =
          SOME (Pair result_lower result_upper) /\
      bounded_object_signed_int result_lower =
        SOME (bounded_signed192_to_int (FST result)) /\
      bounded_object_signed_int result_upper =
        SOME (bounded_signed192_to_int (SND result))
Proof
  Induct_on `products`
  >- (rw [compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def,
          bounded_object_fs_raw_products_acc_def]
      >> simp [])
  >> gen_tac
  >> PairCases_on `h`
  >> rpt gen_tac
  >> strip_tac
  >> fs [compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def]
  >> Cases_on
       `bounded_signed192_add word_lower
          (bounded_signed128_widen192
            (FST (bounded_interval64_raw_mul_bounds_unchecked h0 h1)))`
  >> gvs []
  >> Cases_on
       `bounded_signed192_add word_upper
          (bounded_signed128_widen192
            (SND (bounded_interval64_raw_mul_bounds_unchecked h0 h1)))`
  >> gvs []
  >> mp_tac
       (Q.INST [`left` |-> `h0`, `right` |-> `h1`]
          bounded_interval64_raw_mul_bounds_object_values)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `product_lower`
         (qx_choose_then `product_upper` strip_assume_tac))
  >> fs [LET_THM]
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `object_lower`,
          `left_upper` |-> `object_upper`,
          `right_lower` |-> `product_lower`,
          `right_upper` |-> `product_upper`,
          `left_lower_value` |-> `bounded_signed192_to_int word_lower`,
          `left_upper_value` |-> `bounded_signed192_to_int word_upper`,
          `right_lower_value` |->
            `bounded_signed128_to_int
              (FST (bounded_interval64_raw_mul_bounds_unchecked h0 h1))`,
          `right_upper_value` |->
            `bounded_signed128_to_int
              (SND (bounded_interval64_raw_mul_bounds_unchecked h0 h1))`]
         bounded_object_fs_raw_interval_add_signed_values)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `next_lower`
         (qx_choose_then `next_upper` strip_assume_tac))
  >> imp_res_tac
       compute_boundedWideSignedTheory.bounded_signed192_add_value
  >> fs [compute_boundedTaylorMulTheory.bounded_signed128_widen192_value]
  >> qpat_x_assum
       `!word_lower word_upper object_lower object_upper result. _`
       (mp_tac o Q.SPECL
         [`x`, `x'`, `next_lower`, `next_upper`, `result`])
  >> simp []
  >> disch_then
       (qx_choose_then `result_lower`
         (qx_choose_then `result_upper` strip_assume_tac))
  >> qexists_tac `result_lower`
  >> qexists_tac `result_upper`
  >> simp [bounded_object_fs_raw_products_acc_def]
QED

Theorem bounded_object_fs_fused_products_decimal_from_word:
  bounded_interval64_raw_sum_acc products
      (bounded_signed192_make F bounded192_zero)
      (bounded_signed192_make F bounded192_zero) =
        SOME (word_lower,word_upper) /\
  bounded_signed192_floor64_decimal word_lower = SOME result_lower /\
  bounded_signed192_ceil64_decimal word_upper = SOME result_upper ==>
  ?object_lower object_upper.
    bounded_object_fs_raw_products_acc products
      (Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0))) =
        SOME (Pair object_lower object_upper) /\
    bounded_object_fs_raw_interval_round 1000000000000
      (Pair object_lower object_upper) =
        SOME
          (bounded_interval64_object_cv
            (BoundedInterval64 result_lower result_upper))
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`products`,
          `bounded_signed192_make F bounded192_zero`,
          `bounded_signed192_make F bounded192_zero`,
          `Pair (Num 0) (Num 0)`, `Pair (Num 0) (Num 0)`,
          `(word_lower,word_upper)`]
         bounded_object_fs_raw_products_acc_refines)
  >> impl_tac
  >- simp
       [compute_boundedWideSignedTheory.bounded_signed192_make_value,
        compute_boundedWideTheory.bounded192_zero_def,
        compute_boundedTheory.bounded192_to_num_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` strip_assume_tac))
  >> fs []
  >> metis_tac [bounded_object_fs_raw_interval_round_signed192_exact]
QED

Theorem bounded_object_fs_fused_products_decimal_object_exact:
  bounded_interval64_fused_products_decimal products = SOME result ==>
  ?object_lower object_upper.
    bounded_object_fs_raw_products_acc products
      (Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0))) =
        SOME (Pair object_lower object_upper) /\
    bounded_object_fs_raw_interval_round 1000000000000
      (Pair object_lower object_upper) =
        SOME (bounded_interval64_object_cv result)
Proof
  rw
    [compute_boundedTaylorFusedDecimalTheory.bounded_interval64_fused_products_decimal_def,
     LET_THM]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_object_fs_fused_products_decimal_from_word]
QED

Definition bounded_object_fs_fused_products_decimal_def:
  bounded_object_fs_fused_products_decimal products =
    case bounded_object_fs_raw_products_acc products
      (Pair (Pair (Num 0) (Num 0)) (Pair (Num 0) (Num 0))) of
    | NONE => NONE
    | SOME raw =>
        bounded_object_fs_raw_interval_round 1000000000000 raw
End

Theorem bounded_object_fs_fused_products_decimal_exact:
  bounded_interval64_fused_products_decimal products = SOME result ==>
  bounded_object_fs_fused_products_decimal products =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> drule bounded_object_fs_fused_products_decimal_object_exact
  >> rw [bounded_object_fs_fused_products_decimal_def]
  >> every_case_tac
  >> gvs []
QED

val _ = export_theory ();
