(*****************************************************************************
 * Checked multiplication for compact Taylor states.
 *
 * The product rule is evaluated entirely as data.  Center gradients use
 * g*df + f*dg; the compact upper-triangular Hessian uses
 * g*Hf + df*dg^T + dg*df^T + f*Hg.  The existing complete Taylor
 * constructor then derives whole-box value and gradient bounds.
 *
 * Product-rule sums retain raw 2^80 endpoint products in signed 192-bit
 * accumulators and round outward once after each complete sum.  This matches
 * the normalization boundary required by the genuine checker rather than
 * widening every term independently.
 *****************************************************************************)
Theory compute_boundedTaylorMul
Ancestors
  compute_boundedTaylorAtan
Libs
  bossLib preamble intLib

Definition bounded_signed64_raw_product_def:
  bounded_signed64_raw_product
      (BoundedSigned64 left_negative left_magnitude)
      (BoundedSigned64 right_negative right_magnitude) =
    let product = bounded_word64_mul_full_chunks22
      left_magnitude right_magnitude in
    bounded_signed128_make (¬(left_negative = right_negative))
      (Bounded128 (FST product) (SND product))
End

Definition bounded_signed128_le_words_def:
  bounded_signed128_le_words
      (BoundedSigned128 left_negative left_magnitude)
      (BoundedSigned128 right_negative right_magnitude) =
    if left_negative then
      if right_negative then
        bounded128_le_words right_magnitude left_magnitude
      else T
    else if right_negative then F
    else bounded128_le_words left_magnitude right_magnitude
End

Definition bounded_signed128_min_def:
  bounded_signed128_min left right =
    if bounded_signed128_le_words left right then left else right
End

Definition bounded_signed128_max_def:
  bounded_signed128_max left right =
    if bounded_signed128_le_words left right then right else left
End

Definition bounded_interval64_raw_product_from_pairs_def:
  bounded_interval64_raw_product_from_pairs
      lower_left lower_right upper_left upper_right =
    (bounded_signed64_raw_product lower_left lower_right,
     bounded_signed64_raw_product upper_left upper_right)
End

Definition bounded_interval64_raw_product_mixed_def:
  bounded_interval64_raw_product_mixed
      left_lower left_upper right_lower right_upper =
    let lower_left = bounded_signed64_raw_product left_lower right_upper;
        lower_right = bounded_signed64_raw_product left_upper right_lower;
        upper_left = bounded_signed64_raw_product left_lower right_lower;
        upper_right = bounded_signed64_raw_product left_upper right_upper
    in
      (bounded_signed128_min lower_left lower_right,
       bounded_signed128_max upper_left upper_right)
End

Definition bounded_interval64_raw_mul_bounds_unchecked_def:
  bounded_interval64_raw_mul_bounds_unchecked
      (BoundedInterval64 left_lower left_upper)
      (BoundedInterval64 right_lower right_upper) =
    if bounded_signed64_nonnegative left_lower then
      if bounded_signed64_nonnegative right_lower then
        bounded_interval64_raw_product_from_pairs
          left_lower right_lower left_upper right_upper
      else if bounded_signed64_nonpositive right_upper then
        bounded_interval64_raw_product_from_pairs
          left_upper right_lower left_lower right_upper
      else
        bounded_interval64_raw_product_from_pairs
          left_upper right_lower left_upper right_upper
    else if bounded_signed64_nonpositive left_upper then
      if bounded_signed64_nonnegative right_lower then
        bounded_interval64_raw_product_from_pairs
          left_lower right_upper left_upper right_lower
      else if bounded_signed64_nonpositive right_upper then
        bounded_interval64_raw_product_from_pairs
          left_upper right_upper left_lower right_lower
      else
        bounded_interval64_raw_product_from_pairs
          left_lower right_upper left_lower right_lower
    else if bounded_signed64_nonnegative right_lower then
      bounded_interval64_raw_product_from_pairs
        left_lower right_upper left_upper right_upper
    else if bounded_signed64_nonpositive right_upper then
      bounded_interval64_raw_product_from_pairs
        left_upper right_lower left_lower right_lower
    else
      bounded_interval64_raw_product_mixed
        left_lower left_upper right_lower right_upper
End

Definition bounded_signed128_widen192_def:
  bounded_signed128_widen192
      (BoundedSigned128 negative (Bounded128 high low)) =
    bounded_signed192_make negative (Bounded192 0w high low)
End

Definition bounded_interval64_raw_sum_acc_def:
  bounded_interval64_raw_sum_acc [] lower upper = SOME (lower,upper) ∧
  bounded_interval64_raw_sum_acc ((left,right)::products) lower upper =
    if ¬bounded_interval64_valid left ∨ ¬bounded_interval64_valid right then
      NONE
    else
      let bounds = bounded_interval64_raw_mul_bounds_unchecked left right in
      case bounded_signed192_add lower
        (bounded_signed128_widen192 (FST bounds)) of
      | NONE => NONE
      | SOME next_lower =>
        case bounded_signed192_add upper
          (bounded_signed128_widen192 (SND bounds)) of
        | NONE => NONE
        | SOME next_upper =>
            bounded_interval64_raw_sum_acc products next_lower next_upper
End

Definition bounded_fused_product_input_represents_def:
  bounded_fused_product_input_represents (left,right) exact_value ⇔
    ∃left_value right_value.
      bounded_interval64_contains_int left left_value ∧
      bounded_interval64_contains_int right right_value ∧
      exact_value = left_value * right_value
End

Definition bounded_fused_raw_interval_contains_int_def:
  bounded_fused_raw_interval_contains_int (lower,upper) exact_value ⇔
    bounded_signed192_to_int lower ≤ exact_value ∧
    exact_value ≤ bounded_signed192_to_int upper
End

Definition bounded192_shift_floor40_128_def:
  bounded192_shift_floor40_128 (Bounded192 high middle low) =
    if high >>> 40 ≠ 0w then NONE
    else SOME
      (Bounded128 ((high << 24) + (middle >>> 40))
        ((middle << 24) + (low >>> 40)))
End

Definition bounded192_low40_nonzero_def:
  bounded192_low40_nonzero (Bounded192 high middle low) =
    (word_and low 1099511627775w ≠ 0w)
End

Definition bounded_signed192_shift_floor40_64_def:
  bounded_signed192_shift_floor40_64
      (BoundedSigned192 negative magnitude) =
    case bounded192_shift_floor40_128 magnitude of
    | NONE => NONE
    | SOME quotient =>
      if negative ∧ bounded192_low40_nonzero magnitude then
        bounded_signed128_narrow64_option T
          (bounded128_add_words quotient (Bounded128 0w 1w))
      else bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Definition bounded_signed192_shift_ceil40_64_def:
  bounded_signed192_shift_ceil40_64
      (BoundedSigned192 negative magnitude) =
    case bounded192_shift_floor40_128 magnitude of
    | NONE => NONE
    | SOME quotient =>
      if ¬negative ∧ bounded192_low40_nonzero magnitude then
        bounded_signed128_narrow64_option F
          (bounded128_add_words quotient (Bounded128 0w 1w))
      else bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Definition bounded_interval64_fused_products_def:
  bounded_interval64_fused_products products =
    let zero = bounded_signed192_make F bounded192_zero in
    case bounded_interval64_raw_sum_acc products zero zero of
    | NONE => NONE
    | SOME (raw_lower,raw_upper) =>
      case bounded_signed192_shift_floor40_64 raw_lower of
      | NONE => NONE
      | SOME lower =>
        case bounded_signed192_shift_ceil40_64 raw_upper of
        | NONE => NONE
        | SOME upper => SOME (BoundedInterval64 lower upper)
End

Definition bounded_interval64_fused_scale_add_def:
  bounded_interval64_fused_scale_add left_scale [] right_scale [] = SOME [] ∧
  bounded_interval64_fused_scale_add left_scale (left::left_rest)
      right_scale (right::right_rest) =
    (case bounded_interval64_fused_products
      [(left_scale,left);(right_scale,right)] of
    | NONE => NONE
    | SOME entry =>
      case bounded_interval64_fused_scale_add left_scale left_rest
        right_scale right_rest of
      | NONE => NONE
      | SOME entries => SOME (entry::entries)) ∧
  bounded_interval64_fused_scale_add left_scale _ right_scale _ = NONE
End

Definition bounded_interval64_symmetric_product_pairs_row_def:
  bounded_interval64_symmetric_product_pairs_row
      fixed_left fixed_right [] [] = SOME [] ∧
  bounded_interval64_symmetric_product_pairs_row
      fixed_left fixed_right (left::left_rest) (right::right_rest) =
    (case bounded_interval64_symmetric_product_pairs_row
      fixed_left fixed_right left_rest right_rest of
    | NONE => NONE
    | SOME pairs =>
        SOME (((fixed_left,right),(fixed_right,left))::pairs)) ∧
  bounded_interval64_symmetric_product_pairs_row
      fixed_left fixed_right _ _ = NONE
End

Definition bounded_interval64_symmetric_product_pairs_def:
  bounded_interval64_symmetric_product_pairs [] [] = SOME [] ∧
  bounded_interval64_symmetric_product_pairs (left::left_rest)
      (right::right_rest) =
    (case bounded_interval64_symmetric_product_pairs_row left right
      (left::left_rest) (right::right_rest) of
    | NONE => NONE
    | SOME row =>
      case bounded_interval64_symmetric_product_pairs
        left_rest right_rest of
      | NONE => NONE
      | SOME rows => SOME (row ++ rows)) ∧
  bounded_interval64_symmetric_product_pairs _ _ = NONE
End

Definition bounded_interval64_fused_hessian_def:
  bounded_interval64_fused_hessian left_value right_value [] [] [] =
      SOME [] ∧
  bounded_interval64_fused_hessian left_value right_value
      (left_hessian::left_rest) (right_hessian::right_rest)
      (outer::outer_rest) =
    (case bounded_interval64_fused_products
      [(right_value,left_hessian);FST outer;SND outer;
       (left_value,right_hessian)] of
    | NONE => NONE
    | SOME entry =>
      case bounded_interval64_fused_hessian left_value right_value
        left_rest right_rest outer_rest of
      | NONE => NONE
      | SOME entries => SOME (entry::entries)) ∧
  bounded_interval64_fused_hessian left_value right_value _ _ _ = NONE
End

Definition bounded_interval64_symmetric_outer_def:
  bounded_interval64_symmetric_outer [] [] = SOME [] ∧
  bounded_interval64_symmetric_outer [] (_::_) = NONE ∧
  bounded_interval64_symmetric_outer (_::_) [] = NONE ∧
  bounded_interval64_symmetric_outer
      (left::left_rest) (right::right_rest) =
    case bounded_interval64_list_scale left (right::right_rest) of
    | NONE => NONE
    | SOME left_row =>
      case bounded_interval64_list_scale right (left::left_rest) of
      | NONE => NONE
      | SOME right_row =>
        case bounded_interval64_list_add left_row right_row of
        | NONE => NONE
        | SOME row =>
          case bounded_interval64_symmetric_outer left_rest right_rest of
          | NONE => NONE
          | SOME rows => SOME (row ++ rows)
End

Definition bounded_taylor64_mul_def:
  bounded_taylor64_mul radii left right =
    if ¬bounded_taylor64_well_formed left ∨
       ¬bounded_taylor64_well_formed right
    then NONE
    else
      case left of
      | BoundedTaylor64 left_domain left_center left_center_gradient
          left_value left_gradient_bounds left_hessian =>
        case right of
        | BoundedTaylor64 right_domain right_center right_center_gradient
            right_value right_gradient_bounds right_hessian =>
          case bounded_interval64_mul left_center right_center of
          | NONE => NONE
          | SOME center_value =>
            case bounded_interval64_fused_scale_add
              right_center left_center_gradient
              left_center right_center_gradient of
            | NONE => NONE
            | SOME center_gradient =>
              case bounded_interval64_symmetric_product_pairs
                left_gradient_bounds right_gradient_bounds of
              | NONE => NONE
              | SOME outer_pairs =>
                case bounded_interval64_fused_hessian
                  left_value right_value left_hessian right_hessian
                  outer_pairs of
                | NONE => NONE
                | SOME hessian =>
                    bounded_taylor64_complete radii
                      (left_domain ∧ right_domain) center_value
                      center_gradient hessian
End

Theorem bounded_signed64_raw_product_value:
  bounded_signed128_normalized
    (bounded_signed64_raw_product left right) ∧
  bounded_signed128_to_int
    (bounded_signed64_raw_product left right) =
    bounded_signed64_to_int left * bounded_signed64_to_int right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_signed64_raw_product
          (BoundedSigned64 left_negative left_magnitude)
          (BoundedSigned64 right_negative right_magnitude)`
  >> rw [bounded_signed64_raw_product_def]
  >> mp_tac
       (Q.INST
         [`left` |-> `left_magnitude`, `right` |-> `right_magnitude`]
         compute_boundedTheory.bounded_word64_mul_full_chunks22_correct)
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> simp
       [LET_THM,
        compute_boundedSignedTheory.bounded_signed128_make_normalized,
        compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        compute_boundedTheory.bounded128_to_num_def,
        compute_boundedTheory.bounded_word_base_eq,
        integerTheory.INT_MUL_LNEG, integerTheory.INT_MUL_RNEG,
        integerTheory.INT_MUL]
QED

Theorem bounded_signed128_le_words_correct:
  bounded_signed128_normalized left ∧
  bounded_signed128_normalized right ⇒
  (bounded_signed128_le_words left right ⇔
   bounded_signed128_to_int left ≤ bounded_signed128_to_int right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> rw [bounded_signed128_le_words_def,
         compute_boundedSignedTheory.bounded_signed128_normalized_def,
         compute_boundedSignedEndpointTheory.bounded_signed128_to_int_def,
         compute_boundedSignedAddTheory.bounded128_le_words_correct]
  >> fs [compute_boundedSignedTheory.bounded128_is_zero_iff]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed128_min_value:
  bounded_signed128_normalized left ∧
  bounded_signed128_normalized right ⇒
  bounded_signed128_to_int (bounded_signed128_min left right) =
    (if bounded_signed128_to_int left ≤ bounded_signed128_to_int right then
       bounded_signed128_to_int left
     else bounded_signed128_to_int right)
Proof
  rw [bounded_signed128_min_def, bounded_signed128_le_words_correct]
QED

Theorem bounded_signed128_max_value:
  bounded_signed128_normalized left ∧
  bounded_signed128_normalized right ⇒
  bounded_signed128_to_int (bounded_signed128_max left right) =
    (if bounded_signed128_to_int left ≤ bounded_signed128_to_int right then
       bounded_signed128_to_int right
     else bounded_signed128_to_int left)
Proof
  rw [bounded_signed128_max_def, bounded_signed128_le_words_correct]
QED

Theorem bounded_signed128_min_normalized:
  bounded_signed128_normalized left ∧
  bounded_signed128_normalized right ⇒
  bounded_signed128_normalized (bounded_signed128_min left right)
Proof
  rw [bounded_signed128_min_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_signed128_max_normalized:
  bounded_signed128_normalized left ∧
  bounded_signed128_normalized right ⇒
  bounded_signed128_normalized (bounded_signed128_max left right)
Proof
  rw [bounded_signed128_max_def]
  >> every_case_tac
  >> simp []
QED

Theorem bounded_interval64_raw_product_from_pairs_value:
  let result = bounded_interval64_raw_product_from_pairs
    lower_left lower_right upper_left upper_right in
  bounded_signed128_normalized (FST result) ∧
  bounded_signed128_normalized (SND result) ∧
  bounded_signed128_to_int (FST result) =
    bounded_signed64_to_int lower_left *
      bounded_signed64_to_int lower_right ∧
  bounded_signed128_to_int (SND result) =
    bounded_signed64_to_int upper_left *
      bounded_signed64_to_int upper_right
Proof
  simp [bounded_interval64_raw_product_from_pairs_def, LET_THM,
        bounded_signed64_raw_product_value]
QED

Theorem bounded_interval64_raw_product_mixed_value:
  let result = bounded_interval64_raw_product_mixed
    left_lower left_upper right_lower right_upper in
  bounded_signed128_normalized (FST result) ∧
  bounded_signed128_normalized (SND result) ∧
  bounded_signed128_to_int (FST result) =
    (if bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper ≤
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower
     then bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper
     else bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower) ∧
  bounded_signed128_to_int (SND result) =
    (if bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower ≤
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper
     then bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper
     else bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower)
Proof
  simp [bounded_interval64_raw_product_mixed_def, LET_THM,
        bounded_signed64_raw_product_value,
        bounded_signed128_min_normalized,
        bounded_signed128_max_normalized,
        bounded_signed128_min_value,
        bounded_signed128_max_value]
QED

Theorem bounded_signed128_raw_products_le_correct:
  bounded_signed128_le_words
    (bounded_signed64_raw_product left_lower right_upper)
    (bounded_signed64_raw_product left_upper right_lower) ⇔
  bounded_signed64_to_int left_lower *
      bounded_signed64_to_int right_upper ≤
    bounded_signed64_to_int left_upper *
      bounded_signed64_to_int right_lower
Proof
  simp [bounded_signed128_le_words_correct,
        bounded_signed64_raw_product_value]
QED

fun apply_raw_product_bounds theorem =
  mp_tac
    (INST
      [``left_lower:int`` |->
         ``bounded_signed64_to_int (left_lower:bounded_signed64)``,
       ``left_value:int`` |-> ``(left_value:int)``,
       ``left_upper:int`` |->
         ``bounded_signed64_to_int (left_upper:bounded_signed64)``,
       ``right_lower:int`` |->
         ``bounded_signed64_to_int (right_lower:bounded_signed64)``,
       ``right_value:int`` |-> ``(right_value:int)``,
       ``right_upper:int`` |->
         ``bounded_signed64_to_int (right_upper:bounded_signed64)``]
      theorem)
  >> simp [];

Theorem bounded_interval64_raw_mul_bounds_contains_product:
  bounded_interval64_valid left ∧
  bounded_interval64_valid right ∧
  bounded_interval64_contains_int left left_value ∧
  bounded_interval64_contains_int right right_value ⇒
  let result = bounded_interval64_raw_mul_bounds_unchecked left right in
  bounded_signed128_normalized (FST result) ∧
  bounded_signed128_normalized (SND result) ∧
  bounded_signed128_to_int (FST result) ≤ left_value * right_value ∧
  left_value * right_value ≤ bounded_signed128_to_int (SND result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_interval64_valid
          (BoundedInterval64 left_lower left_upper) ∧
        bounded_interval64_valid
          (BoundedInterval64 right_lower right_upper) ∧ _`
  >> strip_tac
  >> fs [compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> Cases_on `bounded_signed64_nonnegative left_lower`
  >- (Cases_on `bounded_signed64_nonnegative right_lower`
      >- (gvs
           [bounded_interval64_raw_mul_bounds_unchecked_def,
            bounded_interval64_raw_product_from_pairs_def,
            bounded_signed64_raw_product_value,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct]
          >> apply_raw_product_bounds
               compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_nonnegative)
      >> Cases_on `bounded_signed64_nonpositive right_upper`
      >- (gvs
           [bounded_interval64_raw_mul_bounds_unchecked_def,
            bounded_interval64_raw_product_from_pairs_def,
            bounded_signed64_raw_product_value,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> apply_raw_product_bounds
               compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_nonpositive)
      >> gvs
           [bounded_interval64_raw_mul_bounds_unchecked_def,
            bounded_interval64_raw_product_from_pairs_def,
            bounded_signed64_raw_product_value,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> apply_raw_product_bounds
           compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_mixed
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded_signed64_nonpositive left_upper`
  >- (Cases_on `bounded_signed64_nonnegative right_lower`
      >- (gvs
           [bounded_interval64_raw_mul_bounds_unchecked_def,
            bounded_interval64_raw_product_from_pairs_def,
            bounded_signed64_raw_product_value,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> apply_raw_product_bounds
               compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_nonnegative)
      >> Cases_on `bounded_signed64_nonpositive right_upper`
      >- (gvs
           [bounded_interval64_raw_mul_bounds_unchecked_def,
            bounded_interval64_raw_product_from_pairs_def,
            bounded_signed64_raw_product_value,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> apply_raw_product_bounds
               compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_nonpositive)
      >> gvs
           [bounded_interval64_raw_mul_bounds_unchecked_def,
            bounded_interval64_raw_product_from_pairs_def,
            bounded_signed64_raw_product_value,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> apply_raw_product_bounds
           compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_mixed
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded_signed64_nonnegative right_lower`
  >- (gvs
       [bounded_interval64_raw_mul_bounds_unchecked_def,
        bounded_interval64_raw_product_from_pairs_def,
        bounded_signed64_raw_product_value,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> apply_raw_product_bounds
           compute_boundedIntervalTheory.bounded_int_product_bounds_mixed_nonnegative
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded_signed64_nonpositive right_upper`
  >- (gvs
       [bounded_interval64_raw_mul_bounds_unchecked_def,
        bounded_interval64_raw_product_from_pairs_def,
        bounded_signed64_raw_product_value,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> apply_raw_product_bounds
           compute_boundedIntervalTheory.bounded_int_product_bounds_mixed_nonpositive
      >> intLib.ARITH_TAC)
  >> gvs
       [bounded_interval64_raw_mul_bounds_unchecked_def,
        bounded_interval64_raw_product_mixed_def,
        bounded_signed128_min_def,
        bounded_signed128_max_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
  >> every_case_tac
  >> gvs [bounded_signed128_raw_products_le_correct,
          bounded_signed64_raw_product_value]
  >> apply_raw_product_bounds
       compute_boundedIntervalTheory.bounded_int_product_bounds_mixed_mixed
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed128_widen192_value:
  bounded_signed192_normalized (bounded_signed128_widen192 source) ∧
  bounded_signed192_to_int (bounded_signed128_widen192 source) =
    bounded_signed128_to_int source
Proof
  Cases_on `source`
  >> Cases_on `b0`
  >> simp [bounded_signed128_widen192_def,
           compute_boundedWideSignedTheory.bounded_signed192_make_normalized,
           compute_boundedWideSignedTheory.bounded_signed192_make_value,
           compute_boundedSignedEndpointTheory.bounded_signed128_to_int_def,
           compute_boundedTheory.bounded128_to_num_def,
           compute_boundedTheory.bounded192_to_num_def]
QED

Theorem bounded_interval64_raw_mul_bounds_widen_contains_product:
  bounded_interval64_valid left ∧
  bounded_interval64_valid right ∧
  bounded_interval64_contains_int left left_value ∧
  bounded_interval64_contains_int right right_value ⇒
  let bounds = bounded_interval64_raw_mul_bounds_unchecked left right in
  bounded_fused_raw_interval_contains_int
    (bounded_signed128_widen192 (FST bounds),
     bounded_signed128_widen192 (SND bounds))
    (left_value * right_value)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
          [`left` |-> `left`, `right` |-> `right`,
           `left_value` |-> `left_value`,
           `right_value` |-> `right_value`]
          bounded_interval64_raw_mul_bounds_contains_product)
  >> simp [LET_THM, bounded_fused_raw_interval_contains_int_def,
           bounded_signed128_widen192_value]
QED

Theorem bounded_fused_raw_interval_add_contains_int:
  bounded_fused_raw_interval_contains_int left left_value ∧
  bounded_fused_raw_interval_contains_int right right_value ∧
  bounded_signed192_add (FST left) (FST right) = SOME lower ∧
  bounded_signed192_add (SND left) (SND right) = SOME upper ⇒
  bounded_fused_raw_interval_contains_int
    (lower,upper) (left_value + right_value)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_fused_raw_interval_contains_int_def]
  >> imp_res_tac
       compute_boundedWideSignedTheory.bounded_signed192_add_value
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_raw_sum_acc_contains_int:
  ∀products exact_values lower upper accumulator_value result.
    LIST_REL bounded_fused_product_input_represents
      products exact_values ∧
    bounded_fused_raw_interval_contains_int
      (lower,upper) accumulator_value ∧
    bounded_interval64_raw_sum_acc products lower upper = SOME result ⇒
    bounded_fused_raw_interval_contains_int result
      (FOLDL (λtotal value:int. total + value)
        accumulator_value exact_values)
Proof
  Induct
  >- (Cases_on `exact_values`
      >> rw [bounded_interval64_raw_sum_acc_def, LIST_REL_def]
      >> simp [])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `exact_values`
  >> rw [bounded_interval64_raw_sum_acc_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def, bounded_fused_product_input_represents_def]
  >> `bounded_fused_raw_interval_contains_int
        (bounded_signed128_widen192
           (FST (bounded_interval64_raw_mul_bounds_unchecked h0 h1)),
         bounded_signed128_widen192
           (SND (bounded_interval64_raw_mul_bounds_unchecked h0 h1)))
        (left_value * right_value)` by
       (mp_tac
          (Q.INST
            [`left` |-> `h0`, `right` |-> `h1`,
             `left_value` |-> `left_value`,
             `right_value` |-> `right_value`]
            bounded_interval64_raw_mul_bounds_widen_contains_product)
        >> simp [])
  >> `bounded_fused_raw_interval_contains_int (x',x)
        (accumulator_value + left_value * right_value)` by
       (mp_tac
          (Q.INST
            [`left` |-> `(lower,upper)`,
             `right` |->
               `(bounded_signed128_widen192
                   (FST (bounded_interval64_raw_mul_bounds_unchecked h0 h1)),
                 bounded_signed128_widen192
                   (SND (bounded_interval64_raw_mul_bounds_unchecked h0 h1)))`,
             `left_value` |-> `accumulator_value`,
             `right_value` |-> `left_value * right_value`,
             `lower` |-> `x'`, `upper` |-> `x`]
            bounded_fused_raw_interval_add_contains_int)
        >> simp [])
  >> qpat_x_assum
       `∀exact_values lower upper accumulator_value result. _`
       (mp_tac o Q.SPECL
          [`t`, `x'`, `x`,
           `accumulator_value + left_value * right_value`, `result`])
  >> simp []
QED

Theorem bounded192_shift_floor40_128_correct:
  bounded192_shift_floor40_128 value = SOME result ⇒
  bounded128_to_num result =
    bounded192_to_num value DIV 1099511627776
Proof
  Cases_on `value`
  >> rename1 `Bounded192 high middle low`
  >> rw [bounded192_shift_floor40_128_def]
  >> rw [compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded192_to_num_def]
  >> assume_tac
       (Q.INST [`high` |-> `middle`, `low` |-> `low`]
          compute_boundedTheory.bounded_word64_shift_pair40_correct)
  >> assume_tac
       (Q.INST [`high` |-> `high`, `low` |-> `middle`]
          compute_boundedTheory.bounded_word64_shift_pair40_correct)
  >> `w2n (middle << 24 + low >>> 40) =
      w2n (low >>> 40 + middle << 24)` by rw [WORD_ADD_COMM]
  >> `w2n (high << 24 + middle >>> 40) =
      w2n (middle >>> 40 + high << 24)` by rw [WORD_ADD_COMM]
  >> fs []
  >> asm_simp_tac std_ss []
  >> `w2n (high << 24 + middle >>> 40) =
      (w2n middle + bounded_word_base * w2n high) DIV
        1099511627776` by
       (qpat_x_assum
          `w2n (high << 24 + middle >>> 40) +
             bounded_word_base * w2n (high >>> 40) = _` mp_tac
        >> simp [])
  >> fs [w2n_lsr, compute_boundedTheory.bounded_word_base_eq]
  >> `(18446744073709551616 * w2n high + w2n middle) DIV
        1099511627776 =
      16777216 * w2n high + w2n middle DIV 1099511627776` by
       (`18446744073709551616 * w2n high + w2n middle =
          (16777216 * w2n high) * 1099511627776 + w2n middle` by
            CONV_TAC (EQT_INTRO o Grobner.NUM_RING)
        >> asm_rewrite_tac []
        >> simp [arithmeticTheory.ADD_DIV_ADD_DIV])
  >> `(340282366920938463463374607431768211456 * w2n high +
         (w2n low + 18446744073709551616 * w2n middle)) DIV
        1099511627776 =
      18446744073709551616 * 16777216 * w2n high +
        (w2n low + 18446744073709551616 * w2n middle) DIV
          1099511627776` by
       (`340282366920938463463374607431768211456 * w2n high +
          (w2n low + 18446744073709551616 * w2n middle) =
          (18446744073709551616 * 16777216 * w2n high) *
            1099511627776 +
          (w2n low + 18446744073709551616 * w2n middle)` by
            CONV_TAC (EQT_INTRO o Grobner.NUM_RING)
        >> asm_rewrite_tac []
        >> simp [arithmeticTheory.ADD_DIV_ADD_DIV])
  >> fs []
QED

Theorem bounded192_low40_nonzero_correct:
  bounded192_low40_nonzero magnitude ⇔
  bounded192_to_num magnitude MOD 1099511627776 ≠ 0
Proof
  Cases_on `magnitude`
  >> rename1 `Bounded192 high middle low`
  >> `bounded192_to_num (Bounded192 high middle low) MOD
        1099511627776 = w2n low MOD 1099511627776` by
       simp [compute_boundedTheory.bounded192_to_num_def,
             compute_boundedTheory.bounded_word_base_eq,
             arithmeticTheory.ADD_MOD, arithmeticTheory.MOD_TIMES]
  >> asm_rewrite_tac []
  >> rw [bounded192_low40_nonzero_def]
  >> once_rewrite_tac [WORD_AND_COMM]
  >> rw [compute_boundedSignedTheory.bounded_word64_mask40]
  >> `w2n low MOD 1099511627776 < 18446744073709551616` by
       (`w2n low MOD 1099511627776 < 1099511627776` by simp []
        >> intLib.ARITH_TAC)
  >> simp [LESS_MOD]
QED

Theorem bounded_signed192_shift_floor40_64_value:
  bounded_signed192_shift_floor40_64
      (BoundedSigned192 negative magnitude) = SOME result ⇒
  bounded_signed64_to_int result =
    if negative then
      -&(bounded192_to_num magnitude DIV 1099511627776 +
         if bounded192_to_num magnitude MOD 1099511627776 = 0
         then 0 else 1)
    else
      &(bounded192_to_num magnitude DIV 1099511627776)
Proof
  rw [bounded_signed192_shift_floor40_64_def]
  >> every_case_tac
  >> gvs [compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def,
          bounded192_low40_nonzero_correct,
          compute_boundedTheory.bounded128_add_words_refines]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_some
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> fs [compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
         bounded192_shift_floor40_128_correct,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded_word_base_eq]
QED

Theorem bounded_signed192_shift_ceil40_64_value:
  bounded_signed192_shift_ceil40_64
      (BoundedSigned192 negative magnitude) = SOME result ⇒
  bounded_signed64_to_int result =
    if negative then
      -&(bounded192_to_num magnitude DIV 1099511627776)
    else
      &(bounded192_to_num magnitude DIV 1099511627776 +
         if bounded192_to_num magnitude MOD 1099511627776 = 0
         then 0 else 1)
Proof
  rw [bounded_signed192_shift_ceil40_64_def]
  >> every_case_tac
  >> gvs [compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def,
          bounded192_low40_nonzero_correct,
          compute_boundedTheory.bounded128_add_words_refines]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_some
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> fs [compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
         bounded192_shift_floor40_128_correct,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded_word_base_eq]
QED

Theorem bounded_div_ceil40_if_scaled_ge:
  value ≤
    (value DIV 1099511627776 +
       if value MOD 1099511627776 = 0 then 0 else 1) *
      1099511627776
Proof
  mp_tac (Q.SPEC `1099511627776` arithmeticTheory.DIVISION)
  >> simp []
  >> disch_then (qspec_then `value` strip_assume_tac)
  >> Cases_on `value MOD 1099511627776 = 0`
  >> fs [arithmeticTheory.LEFT_ADD_DISTRIB]
  >> qpat_x_assum `value = _` (fn th => once_rewrite_tac [th])
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed192_shift_floor40_64_lower_bound:
  bounded_signed192_shift_floor40_64 source = SOME result ⇒
  (&1099511627776:int) * bounded_signed64_to_int result ≤
    bounded_signed192_to_int source
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> strip_tac
  >> imp_res_tac bounded_signed192_shift_floor40_64_value
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          compute_boundedIntervalTheory.bounded_div_floor40_scaled_le)
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          bounded_div_ceil40_if_scaled_ge)
  >> Cases_on `negative`
  >> fs [compute_boundedWideSignedTheory.bounded_signed192_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_signed192_shift_ceil40_64_upper_bound:
  bounded_signed192_shift_ceil40_64 source = SOME result ⇒
  bounded_signed192_to_int source ≤
    (&1099511627776:int) * bounded_signed64_to_int result
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> strip_tac
  >> imp_res_tac bounded_signed192_shift_ceil40_64_value
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          compute_boundedIntervalTheory.bounded_div_floor40_scaled_le)
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          bounded_div_ceil40_if_scaled_ge)
  >> Cases_on `negative`
  >> fs [compute_boundedWideSignedTheory.bounded_signed192_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_fused_raw_round40_contains_int:
  bounded_fused_raw_interval_contains_int
      (raw_lower,raw_upper) exact_value ∧
  bounded_signed192_shift_floor40_64 raw_lower = SOME lower ∧
  bounded_signed192_shift_ceil40_64 raw_upper = SOME upper ⇒
  bounded_interval64_contains_scaled_int
    (BoundedInterval64 lower upper) (&1099511627776:int) exact_value
Proof
  rw [bounded_fused_raw_interval_contains_int_def,
      compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def]
  >> imp_res_tac bounded_signed192_shift_floor40_64_lower_bound
  >> imp_res_tac bounded_signed192_shift_ceil40_64_upper_bound
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_fused_products_contains_scaled_int:
  LIST_REL bounded_fused_product_input_represents products exact_values ∧
  bounded_interval64_fused_products products = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (FOLDL (λtotal value:int. total + value) 0 exact_values)
Proof
  rw [bounded_interval64_fused_products_def, LET_THM]
  >> every_case_tac
  >> gvs []
  >> `bounded_fused_raw_interval_contains_int
        (bounded_signed192_make F bounded192_zero,
         bounded_signed192_make F bounded192_zero) 0` by
       simp [bounded_fused_raw_interval_contains_int_def,
             compute_boundedWideSignedTheory.bounded_signed192_make_value,
             compute_boundedWideTheory.bounded192_zero_def,
             compute_boundedTheory.bounded192_to_num_def]
  >> imp_res_tac bounded_interval64_raw_sum_acc_contains_int
  >> imp_res_tac bounded_fused_raw_round40_contains_int
QED

Theorem bounded_taylor64_mul_some:
  bounded_taylor64_mul radii left right = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_mul_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some
QED

Theorem bounded_taylor64_mul_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  let tiny = BoundedInterval64
    (BoundedSigned64 F 1w) (BoundedSigned64 F 1w) in
  let malformed = BoundedTaylor64 T one [] one zeros6 zeros21 in
  bounded_interval64_symmetric_outer zeros6 zeros6 = SOME zeros21 ∧
  bounded_interval64_fused_products [(tiny,tiny);(tiny,tiny)] =
    SOME (BoundedInterval64
      (BoundedSigned64 F 0w) (BoundedSigned64 F 1w)) ∧
  bounded_taylor64_mul radii state state = SOME state ∧
  bounded_taylor64_mul radii malformed state = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
