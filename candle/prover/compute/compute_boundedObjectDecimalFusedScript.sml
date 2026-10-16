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

val _ = export_theory ();
