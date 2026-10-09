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
