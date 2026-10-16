(*****************************************************************************
 * Exact object refinement for decimal Taylor completion.
 *
 * This first layer connects the signed-128 gradient-row accumulator to the
 * authenticated object's signed-pair division and outward interval rounding.
 * Later layers lift the dot/quadratic accumulators and result constructor.
 *****************************************************************************)
Theory compute_boundedObjectTaylorCompleteDecimal
Ancestors
  compute_boundedObjectTaylorProductDecimal compute_boundedTaylorCompleteDecimal
Libs
  bossLib preamble intLib

Definition bounded_signed128_object_cv_def:
  bounded_signed128_object_cv
      (BoundedSigned128 negative magnitude) : cv =
    if negative then Pair (Num 0) (Num (bounded128_to_num magnitude))
    else Pair (Num (bounded128_to_num magnitude)) (Num 0)
End

Theorem bounded_object_signed_int_signed128_object_cv[simp]:
  bounded_object_signed_int (bounded_signed128_object_cv value) =
    SOME (bounded_signed128_to_int value)
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> simp
       [bounded_signed128_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedSignedEndpointTheory.bounded_signed128_to_int_def]
QED

Theorem bounded_signed128_floor64_decimal_object_exact:
  bounded_signed128_floor64_decimal source = SOME result ==>
  bounded_object_fs_floor_div
      (bounded_signed128_object_cv source) 1000000000000 =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `source`
  >> Cases_on `b`
  >> rw
       [compute_boundedTaylorCompleteDecimalTheory.bounded_signed128_floor64_decimal_def]
  >> every_case_tac
  >> gvs
       [bounded_signed128_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_decimal,
        compute_boundedTaylorCompleteDecimalTheory.bounded128_floor64_decimal_def,
        compute_boundedTaylorCompleteDecimalTheory.bounded128_ceil64_decimal_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        LET_THM]
  >> fs [compute_boundedTheory.bounded_word_base_eq, LESS_MOD,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> Cases_on `bounded128_to_num b0 = 0`
  >> simp [arithmeticTheory.DIV_EQ_0]
QED

Theorem bounded_signed128_ceil64_decimal_object_exact:
  bounded_signed128_ceil64_decimal source = SOME result ==>
  bounded_object_fs_ceil_div
      (bounded_signed128_object_cv source) 1000000000000 =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `source`
  >> Cases_on `b`
  >> rw
       [compute_boundedTaylorCompleteDecimalTheory.bounded_signed128_ceil64_decimal_def]
  >> every_case_tac
  >> gvs
       [bounded_signed128_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_q_ceil_div_decimal,
        compute_boundedTaylorCompleteDecimalTheory.bounded128_floor64_decimal_def,
        compute_boundedTaylorCompleteDecimalTheory.bounded128_ceil64_decimal_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        LET_THM]
  >> fs [compute_boundedTheory.bounded_word_base_eq, LESS_MOD,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO]
  >> Cases_on `bounded128_to_num b0 = 0`
  >> Cases_on `bounded128_to_num b0 DIV 1000000000000 = 0`
  >> simp []
QED

Theorem bounded_object_fs_raw_interval_round_signed128_exact:
  bounded_object_signed_int object_lower =
      SOME (bounded_signed128_to_int word_lower) /\
  bounded_object_signed_int object_upper =
      SOME (bounded_signed128_to_int word_upper) /\
  bounded_signed128_floor64_decimal word_lower = SOME result_lower /\
  bounded_signed128_ceil64_decimal word_upper = SOME result_upper ==>
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
        (Pair (bounded_signed128_object_cv word_lower)
          (bounded_signed128_object_cv word_upper))` by
       (irule
          compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_extensional
        >> simp [])
  >> pop_assum SUBST1_TAC
  >> irule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_exact
  >> simp [bounded_signed128_floor64_decimal_object_exact,
           bounded_signed128_ceil64_decimal_object_exact]
QED

Definition bounded_object_fs_raw_scale_def:
  bounded_object_fs_raw_scale factor
      (Pair (Num positive) (Num negative) : cv) =
    SOME (Pair (Num (factor * positive)) (Num (factor * negative))) /\
  bounded_object_fs_raw_scale factor _ = NONE
End

Theorem bounded_object_fs_raw_scale_signed_value:
  bounded_object_signed_int source = SOME value /\
  bounded_object_fs_raw_scale factor source = SOME result ==>
  bounded_object_signed_int result = SOME (&factor * value)
Proof
  Cases_on `source`
  >> gvs
       [bounded_object_fs_raw_scale_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [bounded_object_fs_raw_scale_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> strip_tac
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> simp [integerTheory.INT_SUB_LDISTRIB]
QED

Theorem bounded_object_fs_raw_scale_object_cv:
  ?result.
    bounded_object_fs_raw_scale factor
      (bounded_signed64_object_cv value) = SOME result /\
    bounded_object_signed_int result =
      SOME ((&factor:int) * bounded_signed64_to_int value)
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> simp
       [bounded_object_fs_raw_scale_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_scale_decimal128_value:
  bounded_signed128_to_int (bounded_signed64_scale_decimal128 value) =
    (&1000000000000:int) * bounded_signed64_to_int value
Proof
  rw
    [compute_boundedTaylorCompleteDecimalTheory.bounded_signed64_scale_decimal128_def,
     compute_boundedTaylorMulTheory.bounded_signed64_raw_product_value,
     compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> Cases_on `value`
  >> Cases_on `b`
  >> simp
       [compute_boundedTaylorMulTheory.bounded_signed64_raw_product_value,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> simp [integerTheory.INT_MUL_COMM]
QED

Definition bounded_word64_object_cv_def:
  bounded_word64_object_cv (value:word64) : cv =
    Pair (Num (w2n value)) (Num 0)
End

Theorem bounded_word64_object_cv_as_signed64[simp]:
  bounded_word64_object_cv value =
    bounded_signed64_object_cv (BoundedSigned64 F value)
Proof
  simp
    [bounded_word64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
QED

Definition bounded_object_fs_raw_abs_def:
  bounded_object_fs_raw_abs value =
    case bounded_object_fs_raw_neg value of
    | NONE => NONE
    | SOME negative => bounded_object_fs_raw_max value negative
End

Theorem bounded_object_fs_raw_abs_object_cv_exact:
  bounded_object_fs_raw_abs (bounded_signed64_object_cv value) =
    SOME
      (bounded_word64_object_cv
        (bounded_signed64_magnitude value))
Proof
  Cases_on `value`
  >> Cases_on `b`
  >> Cases_on `c = 0w`
  >> simp
       [bounded_object_fs_raw_abs_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_object_cv,
        compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_max_object_cv,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_max_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def]
QED

Definition bounded_object_fs_interval_abs_upper_def:
  bounded_object_fs_interval_abs_upper (Pair lower upper : cv) =
    (case bounded_object_fs_raw_abs lower of
     | NONE => NONE
     | SOME lower_abs =>
       case bounded_object_fs_raw_abs upper of
       | NONE => NONE
       | SOME upper_abs =>
           bounded_object_fs_raw_max lower_abs upper_abs) /\
  bounded_object_fs_interval_abs_upper _ = NONE
End

Theorem bounded_object_fs_interval_abs_upper_exact:
  bounded_object_fs_interval_abs_upper
      (bounded_interval64_object_cv source) =
    SOME
      (bounded_word64_object_cv
        (bounded_interval64_abs_upper source))
Proof
  Cases_on `source`
  >> simp
       [bounded_object_fs_interval_abs_upper_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        bounded_object_fs_raw_abs_object_cv_exact,
        compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_max_object_cv,
        compute_boundedTaylorCompleteTheory.bounded_interval64_abs_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_max_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        LET_THM]
  >> rw
       [wordsTheory.WORD_NOT_LOWER,
        wordsTheory.WORD_LOWER_OR_EQ]
  >> gvs []
QED

Definition bounded_dot_abs_upper_num_def:
  bounded_dot_abs_upper_num [] [] = SOME 0 /\
  bounded_dot_abs_upper_num [] (_::_) = NONE /\
  bounded_dot_abs_upper_num (_::_) [] = NONE /\
  bounded_dot_abs_upper_num (radius::radii) (entry::entries) =
    case bounded_dot_abs_upper_num radii entries of
    | NONE => NONE
    | SOME rest =>
        SOME
          (w2n radius *
             w2n (bounded_interval64_abs_upper entry) + rest)
End

Theorem bounded_dot_abs_upper_acc_num:
  !entries accumulator result.
    bounded_dot_abs_upper_acc radii entries accumulator = SOME result ==>
    ?total.
      bounded_dot_abs_upper_num radii entries = SOME total /\
      bounded128_to_num result = bounded128_to_num accumulator + total
Proof
  Induct_on `radii`
  >> Cases_on `entries`
  >> rw
       [compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def,
        bounded_dot_abs_upper_num_def]
  >> fs [LET_THM]
  >> every_case_tac
  >> gvs []
  >> fs [compute_boundedTheory.bounded128_add_words_refines]
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> res_tac
  >> TRY
       (qexists_tac
         `w2n h * w2n (bounded_interval64_abs_upper h') + total`)
  >> simp
       [compute_boundedTaylorCompleteTheory.bounded_word64_product128_value]
  >> qpat_x_assum
       `bounded_dot_abs_upper_num _ _ = SOME _` mp_tac
  >> simp []
QED

Theorem bounded_dot_abs_upper_num_exact:
  bounded_dot_abs_upper radii entries = SOME result ==>
  bounded_dot_abs_upper_num radii entries =
    SOME (bounded128_to_num result)
Proof
  rw [compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_def]
  >> drule bounded_dot_abs_upper_acc_num
  >> simp
       [compute_boundedTheory.bounded128_to_num_def]
QED

Definition bounded_object_fs_dot_abs_upper_def:
  bounded_object_fs_dot_abs_upper [] entries =
    SOME (Pair (Num 0) (Num 0) : cv) /\
  bounded_object_fs_dot_abs_upper (radius::radii) [] =
    SOME (Pair (Num 0) (Num 0) : cv) /\
  bounded_object_fs_dot_abs_upper (radius::radii) (entry::entries) =
    case bounded_object_fs_interval_abs_upper
      (bounded_interval64_object_cv entry) of
    | NONE => NONE
    | SOME magnitude =>
      case bounded_object_fs_raw_mul
        (bounded_word64_object_cv radius) magnitude of
      | NONE => NONE
      | SOME product =>
        case bounded_object_fs_dot_abs_upper radii entries of
        | NONE => NONE
        | SOME rest => bounded_object_fs_raw_add product rest
End

Theorem bounded_object_fs_dot_abs_upper_num:
  !entries total.
    bounded_dot_abs_upper_num radii entries = SOME total ==>
    ?raw.
      bounded_object_fs_dot_abs_upper radii entries = SOME raw /\
      bounded_object_signed_int raw = SOME (&total:int)
Proof
  Induct_on `radii`
  >> Cases_on `entries`
  >> rw
       [bounded_dot_abs_upper_num_def,
        bounded_object_fs_dot_abs_upper_def]
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `bounded_dot_abs_upper_num radii t`
  >> gvs []
  >> res_tac
  >> rename1
       `bounded_dot_abs_upper_num radii rest_entries = SOME rest_total`
  >> rename1
       `bounded_object_fs_interval_abs_upper
          (bounded_interval64_object_cv entry)`
  >> rename1
       `bounded_signed64_object_cv (BoundedSigned64 F radius)`
  >> mp_tac
       (Q.INST
         [`left` |-> `BoundedSigned64 F radius`,
          `right` |->
            `BoundedSigned64 F (bounded_interval64_abs_upper entry)`]
         compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_mul_object_cv_exists)
  >> disch_then (qx_choose_then `product` assume_tac)
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_mul_signed_value
  >> mp_tac
       (Q.INST
         [`left` |-> `product`, `right` |-> `raw`,
          `left_value` |->
            `(&(w2n (radius:word64)):int) *
             &(w2n (bounded_interval64_abs_upper entry))`,
          `right_value` |-> `(&rest_total:int)`]
         compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_add_signed_value)
  >> impl_tac
  >- simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> disch_then (qx_choose_then `result` strip_assume_tac)
  >> qexists_tac `result`
  >> simp
       [bounded_object_fs_dot_abs_upper_def,
        bounded_object_fs_interval_abs_upper_exact,
        integerTheory.INT_OF_NUM_MUL,
        integerTheory.INT_OF_NUM_ADD,
        integerTheory.INT_ADD_COMM,
        arithmeticTheory.ADD_COMM]
QED

Theorem bounded_object_fs_dot_abs_upper_exact:
  bounded_dot_abs_upper radii entries = SOME result ==>
  ?raw.
    bounded_object_fs_dot_abs_upper radii entries = SOME raw /\
    bounded_object_signed_int raw =
      SOME (&(bounded128_to_num result):int)
Proof
  strip_tac
  >> imp_res_tac bounded_dot_abs_upper_num_exact
  >> metis_tac [bounded_object_fs_dot_abs_upper_num]
QED

Theorem bounded_object_fs_raw_neg_signed_exists:
  bounded_object_signed_int source = SOME value ==>
  ?result.
    bounded_object_fs_raw_neg source = SOME result /\
    bounded_object_signed_int result = SOME (-value)
Proof
  Cases_on `source`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_def]
  >> intLib.ARITH_TAC
QED

Definition bounded_object_fs_gradient_row_def:
  bounded_object_fs_gradient_row radii
      (BoundedInterval64 center_lower center_upper) hessian_row =
    case bounded_object_fs_dot_abs_upper radii hessian_row of
    | NONE => NONE
    | SOME object_variation =>
      case bounded_object_fs_raw_scale 1000000000000
        (bounded_signed64_object_cv center_lower) of
      | NONE => NONE
      | SOME raw_center_lower =>
        case bounded_object_fs_raw_scale 1000000000000
          (bounded_signed64_object_cv center_upper) of
        | NONE => NONE
        | SOME raw_center_upper =>
          case bounded_object_fs_raw_neg object_variation of
          | NONE => NONE
          | SOME negative_variation =>
            case bounded_object_fs_raw_interval_add
              (Pair raw_center_lower raw_center_upper)
              (Pair negative_variation object_variation) of
            | NONE => NONE
            | SOME raw =>
                bounded_object_fs_raw_interval_round 1000000000000 raw
End

Definition bounded_object_fs_gradient_row_from_variation_def:
  bounded_object_fs_gradient_row_from_variation
      (BoundedInterval64 center_lower center_upper) variation =
    case bounded_object_fs_raw_scale 1000000000000
      (bounded_signed64_object_cv center_lower) of
    | NONE => NONE
    | SOME raw_center_lower =>
      case bounded_object_fs_raw_scale 1000000000000
        (bounded_signed64_object_cv center_upper) of
      | NONE => NONE
      | SOME raw_center_upper =>
        let object_variation =
          Pair (Num (bounded128_to_num variation)) (Num 0) in
        case bounded_object_fs_raw_interval_add
          (Pair raw_center_lower raw_center_upper)
          (Pair (Pair (Num 0) (Num (bounded128_to_num variation)))
            object_variation) of
        | NONE => NONE
        | SOME raw =>
            bounded_object_fs_raw_interval_round 1000000000000 raw
End

Theorem bounded_object_fs_gradient_row_from_variation_exact:
  bounded_dot_abs_upper radii hessian_row = SOME variation /\
  bounded_taylor_gradient_row_complete_decimal
      radii center_entry hessian_row = SOME result ==>
  bounded_object_fs_gradient_row_from_variation center_entry variation =
    SOME (bounded_interval64_object_cv result)
Proof
  Cases_on `center_entry`
  >> rw
       [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_row_complete_decimal_def,
        bounded_object_fs_gradient_row_from_variation_def,
        LET_THM]
  >> qpat_x_assum
       `bounded_dot_abs_upper radii hessian_row = SOME variation`
       (fn th => fs [th])
  >> Cases_on
       `bounded_signed128_add (bounded_signed64_scale_decimal128 b)
          (bounded_signed128_make T variation)`
  >> gvs []
  >> Cases_on
       `bounded_signed128_add (bounded_signed64_scale_decimal128 b0)
          (bounded_signed128_make F variation)`
  >> gvs []
  >> Cases_on `bounded_signed128_floor64_decimal x`
  >> gvs []
  >> Cases_on `bounded_signed128_ceil64_decimal x'`
  >> gvs []
  >> rename1
       `bounded_signed128_floor64_decimal word_lower = SOME result_lower`
  >> rename1
       `bounded_signed128_ceil64_decimal word_upper = SOME result_upper`
  >> mp_tac
       (Q.INST
         [`factor` |-> `1000000000000`, `value` |-> `b`]
         bounded_object_fs_raw_scale_object_cv)
  >> disch_then
       (qx_choose_then `raw_center_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`factor` |-> `1000000000000`, `value` |-> `b0`]
         bounded_object_fs_raw_scale_object_cv)
  >> disch_then
       (qx_choose_then `raw_center_upper` strip_assume_tac)
  >> fs []
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `raw_center_lower`,
          `left_upper` |-> `raw_center_upper`,
          `right_lower` |->
            `Pair (Num 0) (Num (bounded128_to_num variation))`,
          `right_upper` |->
            `Pair (Num (bounded128_to_num variation)) (Num 0)`,
          `left_lower_value` |->
            `(&1000000000000:int) * bounded_signed64_to_int b`,
          `left_upper_value` |->
            `(&1000000000000:int) * bounded_signed64_to_int b0`,
          `right_lower_value` |->
            `(0:int) - &(bounded128_to_num variation)`,
          `right_upper_value` |-> `(&(bounded128_to_num variation):int)`]
         compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_signed_values)
  >> impl_tac
  >- simp
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` strip_assume_tac))
  >> fs []
  >> imp_res_tac
       compute_boundedSignedEndpointAddTheory.bounded_signed128_add_value
  >> irule bounded_object_fs_raw_interval_round_signed128_exact
  >> conj_tac
  >- (qexists_tac `word_lower`
      >> simp []
      >> simp
           [bounded_signed64_scale_decimal128_value,
            compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value])
  >> qexists_tac `word_upper`
  >> simp []
  >> simp
       [bounded_signed64_scale_decimal128_value,
        compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value]
QED

Theorem bounded_object_fs_gradient_row_exact:
  bounded_taylor_gradient_row_complete_decimal
      radii center_entry hessian_row = SOME result ==>
  bounded_object_fs_gradient_row radii center_entry hessian_row =
    SOME (bounded_interval64_object_cv result)
Proof
  Cases_on `center_entry`
  >> rw
       [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_row_complete_decimal_def,
        bounded_object_fs_gradient_row_def]
  >> Cases_on `bounded_dot_abs_upper radii hessian_row`
  >> gvs []
  >> rename1
       `bounded_dot_abs_upper radii hessian_row = SOME variation`
  >> Cases_on
       `bounded_signed128_add (bounded_signed64_scale_decimal128 b)
          (bounded_signed128_make T variation)`
  >> gvs []
  >> Cases_on
       `bounded_signed128_add (bounded_signed64_scale_decimal128 b0)
          (bounded_signed128_make F variation)`
  >> gvs []
  >> Cases_on `bounded_signed128_floor64_decimal x`
  >> gvs []
  >> Cases_on `bounded_signed128_ceil64_decimal x'`
  >> gvs []
  >> rename1
       `bounded_signed128_floor64_decimal word_lower = SOME result_lower`
  >> rename1
       `bounded_signed128_ceil64_decimal word_upper = SOME result_upper`
  >> drule bounded_object_fs_dot_abs_upper_exact
  >> disch_then (qx_choose_then `object_variation` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`factor` |-> `1000000000000`, `value` |-> `b`]
         bounded_object_fs_raw_scale_object_cv)
  >> disch_then
       (qx_choose_then `raw_center_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`factor` |-> `1000000000000`, `value` |-> `b0`]
         bounded_object_fs_raw_scale_object_cv)
  >> disch_then
       (qx_choose_then `raw_center_upper` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`source` |-> `object_variation`,
          `value` |-> `(&(bounded128_to_num variation):int)`]
         bounded_object_fs_raw_neg_signed_exists)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `negative_variation` strip_assume_tac)
  >> fs []
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `raw_center_lower`,
          `left_upper` |-> `raw_center_upper`,
          `right_lower` |-> `negative_variation`,
          `right_upper` |-> `object_variation`,
          `left_lower_value` |->
            `(&1000000000000:int) * bounded_signed64_to_int b`,
          `left_upper_value` |->
            `(&1000000000000:int) * bounded_signed64_to_int b0`,
          `right_lower_value` |->
            `(0:int) - &(bounded128_to_num variation)`,
          `right_upper_value` |->
            `(&(bounded128_to_num variation):int)`]
         compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_interval_add_signed_values)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` strip_assume_tac))
  >> fs []
  >> imp_res_tac
       compute_boundedSignedEndpointAddTheory.bounded_signed128_add_value
  >> gvs []
  >> irule bounded_object_fs_raw_interval_round_signed128_exact
  >> conj_tac
  >- (qexists_tac `word_lower`
      >> simp []
      >> simp
           [bounded_signed64_scale_decimal128_value,
            compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value])
  >> qexists_tac `word_upper`
  >> simp []
  >> simp
       [bounded_signed64_scale_decimal128_value,
        compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value]
QED

Definition bounded_object_fs_gradient_rows_def:
  bounded_object_fs_gradient_rows radii [] rows =
    SOME (Num 0 : cv) /\
  bounded_object_fs_gradient_rows radii (center_entry::center_rest) [] =
    SOME (Num 0 : cv) /\
  bounded_object_fs_gradient_rows radii
      (center_entry::center_rest) (hessian_row::hessian_rest) =
    case bounded_object_fs_gradient_row radii center_entry hessian_row of
    | NONE => NONE
    | SOME gradient_bound =>
      case bounded_object_fs_gradient_rows
        radii center_rest hessian_rest of
      | NONE => NONE
      | SOME gradient_rest => SOME (Pair gradient_bound gradient_rest)
End

Theorem bounded_object_fs_gradient_rows_exact:
  !hessian_rows result.
    bounded_taylor_gradient_rows_complete_decimal
      radii center_gradient hessian_rows = SOME result ==>
    bounded_object_fs_gradient_rows radii center_gradient hessian_rows =
      SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `center_gradient`
  >> Cases_on `hessian_rows`
  >> rw
       [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_rows_complete_decimal_def,
        bounded_object_fs_gradient_rows_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> imp_res_tac bounded_object_fs_gradient_row_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_gradient_complete_def:
  bounded_object_fs_gradient_complete radii center_gradient hessian =
    case bounded_hessian64_rows hessian of
    | NONE => NONE
    | SOME rows =>
        bounded_object_fs_gradient_rows radii center_gradient rows
End

Theorem bounded_object_fs_gradient_complete_exact:
  bounded_taylor_gradient_complete_decimal
      radii center_gradient hessian = SOME result ==>
  bounded_object_fs_gradient_complete radii center_gradient hessian =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw
    [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_complete_decimal_def,
     bounded_object_fs_gradient_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_object_fs_gradient_rows_exact
QED

val _ = export_theory ();
