(*****************************************************************************
 * Exact interval-operation bridge for the authenticated decimal object
 * checker.  This layer deliberately follows the source checker's operation
 * order: form raw signed products first, then apply directed decimal
 * rounding to the two selected endpoints.
 *****************************************************************************)
Theory compute_boundedObjectDecimalInterval
Ancestors
  compute_boundedObjectDecimalOrder
Libs
  bossLib preamble intLib

Definition bounded_object_int_min_def:
  bounded_object_int_min (left:int) right =
    if left <= right then left else right
End

Definition bounded_object_int_max_def:
  bounded_object_int_max (left:int) right =
    if left <= right then right else left
End

Definition bounded_object_int_min4_def:
  bounded_object_int_min4 first second third fourth =
    bounded_object_int_min
      (bounded_object_int_min first second)
      (bounded_object_int_min third fourth)
End

Definition bounded_object_int_max4_def:
  bounded_object_int_max4 first second third fourth =
    bounded_object_int_max
      (bounded_object_int_max first second)
      (bounded_object_int_max third fourth)
End

Theorem bounded_object_int_min4_eq_member:
  (candidate = first_value \/ candidate = second_value \/
   candidate = third_value \/ candidate = fourth_value) /\
  candidate <= first_value /\
  candidate <= second_value /\
  candidate <= third_value /\
  candidate <= fourth_value ==>
  bounded_object_int_min4 first_value second_value
      third_value fourth_value = candidate
Proof
  rw [bounded_object_int_min4_def, bounded_object_int_min_def]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_int_max4_eq_member:
  (candidate = first_value \/ candidate = second_value \/
   candidate = third_value \/ candidate = fourth_value) /\
  first_value <= candidate /\
  second_value <= candidate /\
  third_value <= candidate /\
  fourth_value <= candidate ==>
  bounded_object_int_max4 first_value second_value
      third_value fourth_value = candidate
Proof
  rw [bounded_object_int_max4_def, bounded_object_int_max_def]
  >> every_case_tac
  >> gvs []
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_int_min_is_member:
  bounded_object_int_min left right = left \/
  bounded_object_int_min left right = right
Proof
  rw [bounded_object_int_min_def]
QED

Theorem bounded_object_int_max_is_member:
  bounded_object_int_max left right = left \/
  bounded_object_int_max left right = right
Proof
  rw [bounded_object_int_max_def]
QED

Theorem bounded_object_int_min_le_from_disj:
  ((left:int) <= value \/ right <= value) ==>
  bounded_object_int_min left right <= value
Proof
  rw [bounded_object_int_min_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_int_le_max_from_disj:
  ((value:int) <= left \/ value <= right) ==>
  value <= bounded_object_int_max left right
Proof
  rw [bounded_object_int_max_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_int_product_extrema_from_bounds:
  left_lower <= left_upper /\
  right_lower <= right_upper /\
  (lower = left_lower * right_lower \/
   lower = left_lower * right_upper \/
   lower = left_upper * right_lower \/
   lower = left_upper * right_upper) /\
  (upper = left_lower * right_lower \/
   upper = left_lower * right_upper \/
   upper = left_upper * right_lower \/
   upper = left_upper * right_upper) /\
  (!left_value right_value.
     left_lower <= left_value /\ left_value <= left_upper /\
     right_lower <= right_value /\ right_value <= right_upper ==>
     lower <= left_value * right_value /\
     left_value * right_value <= upper) ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) = lower /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) = upper
Proof
  disch_tac
  >> conj_tac
  >- (irule bounded_object_int_min4_eq_member
      >> fs [])
  >> irule bounded_object_int_max4_eq_member
  >> fs []
QED

Theorem bounded_object_int_product_extrema_nonnegative_nonnegative:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  0 <= left_lower /\ 0 <= right_lower ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_lower /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_upper
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> irule
       compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_nonnegative
  >> simp []
QED

Theorem bounded_object_int_product_extrema_nonnegative_nonpositive:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  0 <= left_lower /\ right_upper <= 0 ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_lower /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_upper
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> irule
       compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_nonpositive
  >> simp []
QED

Theorem bounded_object_int_product_extrema_nonpositive_nonnegative:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  left_upper <= 0 /\ 0 <= right_lower ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_upper /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_lower
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> irule
       compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_nonnegative
  >> simp []
QED

Theorem bounded_object_int_product_extrema_nonpositive_nonpositive:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  left_upper <= 0 /\ right_upper <= 0 ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_upper /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_lower
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> irule
       compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_nonpositive
  >> simp []
QED

Theorem bounded_object_int_product_extrema_nonnegative_mixed:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  0 <= left_lower /\ right_lower <= 0 /\ 0 <= right_upper ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_lower /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_upper
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> mp_tac
       compute_boundedIntervalTheory.bounded_int_product_bounds_nonnegative_mixed
  >> simp []
QED

Theorem bounded_object_int_product_extrema_nonpositive_mixed:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  left_upper <= 0 /\ right_lower <= 0 /\ 0 <= right_upper ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_upper /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_lower
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> mp_tac
       compute_boundedIntervalTheory.bounded_int_product_bounds_nonpositive_mixed
  >> simp []
QED

Theorem bounded_object_int_product_extrema_mixed_nonnegative:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  left_lower <= 0 /\ 0 <= left_upper /\ 0 <= right_lower ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_upper /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_upper
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> mp_tac
       compute_boundedIntervalTheory.bounded_int_product_bounds_mixed_nonnegative
  >> simp []
QED

Theorem bounded_object_int_product_extrema_mixed_nonpositive:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  left_lower <= 0 /\ 0 <= left_upper /\ right_upper <= 0 ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_upper * right_lower /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        left_lower * right_lower
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp []
  >> rpt gen_tac
  >> disch_tac
  >> mp_tac
       compute_boundedIntervalTheory.bounded_int_product_bounds_mixed_nonpositive
  >> simp []
QED

Theorem bounded_object_int_product_extrema_mixed_mixed:
  left_lower <= left_upper /\ right_lower <= right_upper /\
  left_lower <= 0 /\ 0 <= left_upper /\
  right_lower <= 0 /\ 0 <= right_upper ==>
  bounded_object_int_min4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        bounded_object_int_min
          (left_lower * right_upper) (left_upper * right_lower) /\
  bounded_object_int_max4
      (left_lower * right_lower) (left_lower * right_upper)
      (left_upper * right_lower) (left_upper * right_upper) =
        bounded_object_int_max
          (left_lower * right_lower) (left_upper * right_upper)
Proof
  strip_tac
  >> irule bounded_object_int_product_extrema_from_bounds
  >> simp [bounded_object_int_min_is_member,
           bounded_object_int_max_is_member]
  >> conj_tac
  >- (rpt gen_tac
      >> disch_tac
      >> mp_tac
           compute_boundedIntervalTheory.bounded_int_product_bounds_mixed_mixed
      >> impl_tac
      >- simp []
      >> disch_tac
      >> conj_tac
      >- (irule bounded_object_int_min_le_from_disj
          >> simp [])
      >> irule bounded_object_int_le_max_from_disj
      >> simp [])
  >> rw [bounded_object_int_min_def, bounded_object_int_max_def]
QED

Definition bounded_object_fs_raw_interval_extrema_def:
  bounded_object_fs_raw_interval_extrema first second third fourth =
    case bounded_object_fs_raw_min first second of
    | NONE => NONE
    | SOME lower_left =>
      case bounded_object_fs_raw_min third fourth of
      | NONE => NONE
      | SOME lower_right =>
        case bounded_object_fs_raw_min lower_left lower_right of
        | NONE => NONE
        | SOME lower =>
          case bounded_object_fs_raw_max first second of
          | NONE => NONE
          | SOME upper_left =>
            case bounded_object_fs_raw_max third fourth of
            | NONE => NONE
            | SOME upper_right =>
              case bounded_object_fs_raw_max upper_left upper_right of
              | NONE => NONE
              | SOME upper => SOME (Pair lower upper)
End

Theorem bounded_object_fs_raw_interval_extrema_signed_values:
  bounded_object_signed_int first_raw = SOME first_value /\
  bounded_object_signed_int second_raw = SOME second_value /\
  bounded_object_signed_int third_raw = SOME third_value /\
  bounded_object_signed_int fourth_raw = SOME fourth_value /\
  bounded_object_fs_raw_interval_extrema
      first_raw second_raw third_raw fourth_raw =
      SOME (Pair lower upper) ==>
  bounded_object_signed_int lower =
      SOME
        (bounded_object_int_min4 first_value second_value
          third_value fourth_value) /\
  bounded_object_signed_int upper =
      SOME
        (bounded_object_int_max4 first_value second_value
          third_value fourth_value)
Proof
  strip_tac
  >> fs [bounded_object_int_min4_def,
         bounded_object_int_max4_def,
         bounded_object_int_min_def,
         bounded_object_int_max_def]
  >> Cases_on `first_value <= second_value`
  >> Cases_on `third_value <= fourth_value`
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_min_signed_ints
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_max_signed_ints
  >> gvs [bounded_object_fs_raw_interval_extrema_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_fs_raw_interval_extrema_exists:
  bounded_object_signed_int first_raw = SOME first_value /\
  bounded_object_signed_int second_raw = SOME second_value /\
  bounded_object_signed_int third_raw = SOME third_value /\
  bounded_object_signed_int fourth_raw = SOME fourth_value ==>
  ?lower upper.
    bounded_object_fs_raw_interval_extrema
      first_raw second_raw third_raw fourth_raw =
      SOME (Pair lower upper)
Proof
  strip_tac
  >> simp [bounded_object_fs_raw_interval_extrema_def]
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_min_signed_ints
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_max_signed_ints
  >> Cases_on `first_value <= second_value`
  >> Cases_on `third_value <= fourth_value`
  >> gvs []
QED

Definition bounded_object_fs_raw_interval_mul_def:
  bounded_object_fs_raw_interval_mul
      (Pair left_lower left_upper : cv)
      (Pair right_lower right_upper : cv) =
    (case bounded_object_fs_raw_mul left_lower right_lower of
     | NONE => NONE
     | SOME lower_lower =>
       case bounded_object_fs_raw_mul left_lower right_upper of
       | NONE => NONE
       | SOME lower_upper =>
         case bounded_object_fs_raw_mul left_upper right_lower of
         | NONE => NONE
         | SOME upper_lower =>
           case bounded_object_fs_raw_mul left_upper right_upper of
           | NONE => NONE
           | SOME upper_upper =>
             bounded_object_fs_raw_interval_extrema
               lower_lower lower_upper upper_lower upper_upper) /\
  bounded_object_fs_raw_interval_mul _ _ = NONE
End

Theorem bounded_object_fs_raw_mul_object_cv_exists:
  ?raw.
    bounded_object_fs_raw_mul
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) = SOME raw
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> simp
       [compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_raw_mul_def]
QED

Theorem bounded_object_fs_raw_interval_mul_signed_values:
  bounded_object_fs_raw_interval_mul
      (Pair
        (bounded_signed64_object_cv left_lower)
        (bounded_signed64_object_cv left_upper))
      (Pair
        (bounded_signed64_object_cv right_lower)
        (bounded_signed64_object_cv right_upper)) =
      SOME (Pair lower upper) ==>
  bounded_object_signed_int lower =
    SOME
      (bounded_object_int_min4
        (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower)
        (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper)
        (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower)
        (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper)) /\
  bounded_object_signed_int upper =
    SOME
      (bounded_object_int_max4
        (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower)
        (bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper)
        (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower)
        (bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper))
Proof
  rw [bounded_object_fs_raw_interval_mul_def]
  >> Cases_on
       `bounded_object_fs_raw_mul
          (bounded_signed64_object_cv left_lower)
          (bounded_signed64_object_cv right_lower)`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_raw_mul
          (bounded_signed64_object_cv left_lower)
          (bounded_signed64_object_cv right_upper)`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_raw_mul
          (bounded_signed64_object_cv left_upper)
          (bounded_signed64_object_cv right_lower)`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_raw_mul
          (bounded_signed64_object_cv left_upper)
          (bounded_signed64_object_cv right_upper)`
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_mul_signed_value
  >> imp_res_tac bounded_object_fs_raw_interval_extrema_signed_values
  >> gvs []
QED

Theorem bounded_object_fs_raw_interval_mul_object_cv_exists:
  ?lower upper.
    bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv
        (BoundedInterval64 left_lower left_upper))
      (bounded_interval64_object_cv
        (BoundedInterval64 right_lower right_upper)) =
      SOME (Pair lower upper)
Proof
  mp_tac
    (Q.INST [`left` |-> `left_lower`, `right` |-> `right_lower`]
      bounded_object_fs_raw_mul_object_cv_exists)
  >> disch_then (qx_choose_then `lower_lower` assume_tac)
  >> mp_tac
    (Q.INST [`left` |-> `left_lower`, `right` |-> `right_upper`]
      bounded_object_fs_raw_mul_object_cv_exists)
  >> disch_then (qx_choose_then `lower_upper` assume_tac)
  >> mp_tac
    (Q.INST [`left` |-> `left_upper`, `right` |-> `right_lower`]
      bounded_object_fs_raw_mul_object_cv_exists)
  >> disch_then (qx_choose_then `upper_lower` assume_tac)
  >> mp_tac
    (Q.INST [`left` |-> `left_upper`, `right` |-> `right_upper`]
      bounded_object_fs_raw_mul_object_cv_exists)
  >> disch_then (qx_choose_then `upper_upper` assume_tac)
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_mul_signed_value
  >> fs [bounded_object_fs_raw_interval_mul_def,
         compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> metis_tac [bounded_object_fs_raw_interval_extrema_exists]
QED

Definition bounded_object_fs_raw_interval_round_def:
  bounded_object_fs_raw_interval_round denominator
      (Pair lower upper : cv) =
    (case bounded_object_fs_floor_div lower denominator of
     | NONE => NONE
     | SOME rounded_lower =>
         case bounded_object_fs_ceil_div upper denominator of
         | NONE => NONE
         | SOME rounded_upper => SOME (Pair rounded_lower rounded_upper)) /\
  bounded_object_fs_raw_interval_round denominator _ = NONE
End

Theorem bounded_object_fs_raw_interval_round_exact:
  bounded_object_fs_floor_div raw_lower denominator =
      SOME (bounded_signed64_object_cv lower) /\
  bounded_object_fs_ceil_div raw_upper denominator =
      SOME (bounded_signed64_object_cv upper) ==>
  bounded_object_fs_raw_interval_round denominator
      (Pair raw_lower raw_upper) =
    SOME
      (bounded_interval64_object_cv
        (BoundedInterval64 lower upper))
Proof
  simp [bounded_object_fs_raw_interval_round_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
QED

Theorem bounded_object_fs_raw_interval_round_extensional:
  bounded_object_signed_int first_lower = SOME lower_value /\
  bounded_object_signed_int second_lower = SOME lower_value /\
  bounded_object_signed_int first_upper = SOME upper_value /\
  bounded_object_signed_int second_upper = SOME upper_value ==>
  bounded_object_fs_raw_interval_round denominator
      (Pair first_lower first_upper) =
    bounded_object_fs_raw_interval_round denominator
      (Pair second_lower second_upper)
Proof
  strip_tac
  >> `bounded_object_fs_floor_div first_lower denominator =
      bounded_object_fs_floor_div second_lower denominator` by
       metis_tac
         [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_floor_div_extensional]
  >> `bounded_object_fs_ceil_div first_upper denominator =
      bounded_object_fs_ceil_div second_upper denominator` by
       metis_tac
         [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_ceil_div_extensional]
  >> simp [bounded_object_fs_raw_interval_round_def]
QED

Theorem bounded_object_fs_raw_interval_mul_round_selected:
  bounded_object_fs_raw_interval_mul
      (Pair
        (bounded_signed64_object_cv left_lower)
        (bounded_signed64_object_cv left_upper))
      (Pair
        (bounded_signed64_object_cv right_lower)
        (bounded_signed64_object_cv right_upper)) =
      SOME (Pair object_lower object_upper) /\
  bounded_object_fs_raw_mul
      (bounded_signed64_object_cv selected_lower_left)
      (bounded_signed64_object_cv selected_lower_right) =
      SOME selected_lower /\
  bounded_object_fs_raw_mul
      (bounded_signed64_object_cv selected_upper_left)
      (bounded_signed64_object_cv selected_upper_right) =
      SOME selected_upper /\
  bounded_object_int_min4
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper) =
    bounded_signed64_to_int selected_lower_left *
      bounded_signed64_to_int selected_lower_right /\
  bounded_object_int_max4
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper) =
    bounded_signed64_to_int selected_upper_left *
      bounded_signed64_to_int selected_upper_right ==>
  bounded_object_fs_raw_interval_round denominator
      (Pair selected_lower selected_upper) =
    bounded_object_fs_raw_interval_round denominator
      (Pair object_lower object_upper)
Proof
  strip_tac
  >> imp_res_tac bounded_object_fs_raw_interval_mul_signed_values
  >> imp_res_tac
       compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_mul_signed_value
  >> irule bounded_object_fs_raw_interval_round_extensional
  >> gvs []
QED

Definition bounded_object_fs_interval_mul_decimal_def:
  bounded_object_fs_interval_mul_decimal left right =
    case bounded_object_fs_raw_interval_mul left right of
    | NONE => NONE
    | SOME raw =>
        bounded_object_fs_raw_interval_round 1000000000000 raw
End

Theorem bounded_interval64_product_from_pairs_decimal_object_exact:
  bounded_signed64_normalized lower_left /\
  bounded_signed64_normalized lower_right /\
  bounded_signed64_normalized upper_left /\
  bounded_signed64_normalized upper_right /\
  bounded_interval64_product_from_pairs_decimal
      lower_left lower_right upper_left upper_right = SOME result ==>
  ?raw_lower raw_upper.
    bounded_object_fs_raw_mul
      (bounded_signed64_object_cv lower_left)
      (bounded_signed64_object_cv lower_right) = SOME raw_lower /\
    bounded_object_fs_raw_mul
      (bounded_signed64_object_cv upper_left)
      (bounded_signed64_object_cv upper_right) = SOME raw_upper /\
    bounded_object_fs_raw_interval_round 1000000000000
      (Pair raw_lower raw_upper) =
        SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def]
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal lower_left lower_right`
  >> gvs []
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal upper_left upper_right`
  >> gvs []
  >> mp_tac
       (Q.INST
         [`left` |-> `lower_left`,
          `right` |-> `lower_right`,
          `result` |-> `x`]
         compute_boundedObjectDecimalArithmeticTheory.bounded_scaled_mul_floor64_decimal_object_exact)
  >> impl_tac
  >- simp []
  >> disch_then (qx_choose_then `raw_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`left` |-> `upper_left`,
          `right` |-> `upper_right`,
          `result` |-> `x'`]
         compute_boundedObjectDecimalArithmeticTheory.bounded_scaled_mul_ceil64_decimal_object_exact)
  >> impl_tac
  >- simp []
  >> disch_then (qx_choose_then `raw_upper` strip_assume_tac)
  >> qexists_tac `raw_lower`
  >> qexists_tac `raw_upper`
  >> simp [bounded_object_fs_raw_interval_round_def,
           compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
QED

Theorem bounded_object_fs_interval_mul_decimal_from_pairs_exact:
  bounded_signed64_normalized left_lower /\
  bounded_signed64_normalized left_upper /\
  bounded_signed64_normalized right_lower /\
  bounded_signed64_normalized right_upper /\
  bounded_signed64_normalized selected_lower_left /\
  bounded_signed64_normalized selected_lower_right /\
  bounded_signed64_normalized selected_upper_left /\
  bounded_signed64_normalized selected_upper_right /\
  bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv
        (BoundedInterval64 left_lower left_upper))
      (bounded_interval64_object_cv
        (BoundedInterval64 right_lower right_upper)) =
      SOME (Pair object_lower object_upper) /\
  bounded_object_int_min4
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper) =
    bounded_signed64_to_int selected_lower_left *
      bounded_signed64_to_int selected_lower_right /\
  bounded_object_int_max4
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_lower *
        bounded_signed64_to_int right_upper)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_lower)
      (bounded_signed64_to_int left_upper *
        bounded_signed64_to_int right_upper) =
    bounded_signed64_to_int selected_upper_left *
      bounded_signed64_to_int selected_upper_right /\
  bounded_interval64_product_from_pairs_decimal
      selected_lower_left selected_lower_right
      selected_upper_left selected_upper_right = SOME result ==>
  bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv
        (BoundedInterval64 left_lower left_upper))
      (bounded_interval64_object_cv
        (BoundedInterval64 right_lower right_upper)) =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`lower_left` |-> `selected_lower_left`,
          `lower_right` |-> `selected_lower_right`,
          `upper_left` |-> `selected_upper_left`,
          `upper_right` |-> `selected_upper_right`,
          `result` |-> `result`]
         bounded_interval64_product_from_pairs_decimal_object_exact)
  >> impl_tac
  >- simp []
  >> disch_then
       (qx_choose_then `raw_lower`
         (qx_choose_then `raw_upper` strip_assume_tac))
  >> fs [bounded_object_fs_interval_mul_decimal_def,
         compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> metis_tac [bounded_object_fs_raw_interval_mul_round_selected]
QED

Theorem bounded_scaled_mul_floor64_decimal_cross_order:
  ~bounded_signed64_nonnegative negative_left /\
  ~bounded_signed64_nonpositive positive_right /\
  ~bounded_signed64_nonpositive positive_left /\
  ~bounded_signed64_nonnegative negative_right /\
  bounded_signed64_to_int negative_left *
      bounded_signed64_to_int positive_right <=
    bounded_signed64_to_int positive_left *
      bounded_signed64_to_int negative_right /\
  bounded_scaled_mul_floor64_decimal negative_left positive_right =
      SOME first_result /\
  bounded_scaled_mul_floor64_decimal positive_left negative_right =
      SOME second_result ==>
  bounded_signed64_le first_result second_result
Proof
  Cases_on `negative_left`
  >> Cases_on `positive_right`
  >> Cases_on `positive_left`
  >> Cases_on `negative_right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> Cases_on `b''`
  >> Cases_on `b'''`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_value
  >> gvs
       [compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> fs [integerTheory.INT_MUL_LNEG,
         integerTheory.INT_MUL_RNEG,
         integerTheory.INT_MUL]
  >> irule arithmeticTheory.DIV_LE_MONOTONE
  >> simp []
QED

Theorem bounded_scaled_mul_ceil64_decimal_same_sign_order:
  ~bounded_signed64_nonnegative negative_left /\
  ~bounded_signed64_nonpositive positive_right /\
  ~bounded_signed64_nonpositive positive_left /\
  ~bounded_signed64_nonnegative negative_right /\
  bounded_signed64_to_int negative_left *
      bounded_signed64_to_int negative_right <=
    bounded_signed64_to_int positive_left *
      bounded_signed64_to_int positive_right /\
  bounded_scaled_mul_ceil64_decimal negative_left negative_right =
      SOME first_result /\
  bounded_scaled_mul_ceil64_decimal positive_left positive_right =
      SOME second_result ==>
  bounded_signed64_le first_result second_result
Proof
  Cases_on `negative_left`
  >> Cases_on `positive_right`
  >> Cases_on `positive_left`
  >> Cases_on `negative_right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> Cases_on `b''`
  >> Cases_on `b'''`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_value
  >> gvs
       [compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> fs [integerTheory.INT_MUL_LNEG,
         integerTheory.INT_MUL_RNEG,
         integerTheory.INT_MUL]
  >> irule arithmeticTheory.DIV_LE_MONOTONE
  >> simp []
QED

Theorem bounded_scaled_mul_floor64_decimal_cross_reverse_order:
  ~bounded_signed64_nonnegative negative_left /\
  ~bounded_signed64_nonpositive positive_right /\
  ~bounded_signed64_nonpositive positive_left /\
  ~bounded_signed64_nonnegative negative_right /\
  bounded_signed64_to_int positive_left *
      bounded_signed64_to_int negative_right <=
    bounded_signed64_to_int negative_left *
      bounded_signed64_to_int positive_right /\
  bounded_scaled_mul_floor64_decimal negative_left positive_right =
      SOME first_result /\
  bounded_scaled_mul_floor64_decimal positive_left negative_right =
      SOME second_result ==>
  bounded_signed64_le second_result first_result
Proof
  Cases_on `negative_left`
  >> Cases_on `positive_right`
  >> Cases_on `positive_left`
  >> Cases_on `negative_right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> Cases_on `b''`
  >> Cases_on `b'''`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_value
  >> gvs
       [compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> fs [integerTheory.INT_MUL_LNEG,
         integerTheory.INT_MUL_RNEG,
         integerTheory.INT_MUL]
  >> irule arithmeticTheory.DIV_LE_MONOTONE
  >> simp []
QED

Theorem bounded_scaled_mul_ceil64_decimal_same_sign_reverse_order:
  ~bounded_signed64_nonnegative negative_left /\
  ~bounded_signed64_nonpositive positive_right /\
  ~bounded_signed64_nonpositive positive_left /\
  ~bounded_signed64_nonnegative negative_right /\
  bounded_signed64_to_int positive_left *
      bounded_signed64_to_int positive_right <=
    bounded_signed64_to_int negative_left *
      bounded_signed64_to_int negative_right /\
  bounded_scaled_mul_ceil64_decimal negative_left negative_right =
      SOME first_result /\
  bounded_scaled_mul_ceil64_decimal positive_left positive_right =
      SOME second_result ==>
  bounded_signed64_le second_result first_result
Proof
  Cases_on `negative_left`
  >> Cases_on `positive_right`
  >> Cases_on `positive_left`
  >> Cases_on `negative_right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> Cases_on `b''`
  >> Cases_on `b'''`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_value
  >> gvs
       [compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> fs [integerTheory.INT_MUL_LNEG,
         integerTheory.INT_MUL_RNEG,
         integerTheory.INT_MUL]
  >> irule arithmeticTheory.DIV_LE_MONOTONE
  >> simp []
QED

Theorem bounded_signed64_to_int_injective_normalized:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right /\
  bounded_signed64_to_int left = bounded_signed64_to_int right ==>
  left = right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `b`
  >> Cases_on `b'`
  >> simp
       [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_min_reverse_order:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right /\
  bounded_signed64_le right left ==>
  bounded_signed64_min left right = right
Proof
  strip_tac
  >> Cases_on `bounded_signed64_le left right`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_min_def]
  >> metis_tac
       [compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        bounded_signed64_to_int_injective_normalized,
        integerTheory.INT_LE_ANTISYM]
QED

Theorem bounded_signed64_max_reverse_order:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right /\
  bounded_signed64_le right left ==>
  bounded_signed64_max left right = left
Proof
  strip_tac
  >> Cases_on `bounded_signed64_le left right`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_max_def]
  >> metis_tac
       [compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        bounded_signed64_to_int_injective_normalized,
        integerTheory.INT_LE_ANTISYM]
QED

Theorem bounded_object_fs_interval_mul_decimal_mixed_exact:
  bounded_interval64_valid (BoundedInterval64 left_lower left_upper) /\
  bounded_interval64_valid (BoundedInterval64 right_lower right_upper) /\
  ~bounded_signed64_nonnegative left_lower /\
  ~bounded_signed64_nonpositive left_upper /\
  ~bounded_signed64_nonnegative right_lower /\
  ~bounded_signed64_nonpositive right_upper /\
  bounded_interval64_product_mixed_decimal
      left_lower left_upper right_lower right_upper = SOME result ==>
  bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv
        (BoundedInterval64 left_lower left_upper))
      (bounded_interval64_object_cv
        (BoundedInterval64 right_lower right_upper)) =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `left_lower`,
          `left_upper` |-> `left_upper`,
          `right_lower` |-> `right_lower`,
          `right_upper` |-> `right_upper`]
         bounded_object_fs_raw_interval_mul_object_cv_exists)
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` assume_tac))
  >> mp_tac
       (INST
         [``(left_lower:int)`` |->
            ``bounded_signed64_to_int (left_lower:bounded_signed64)``,
          ``(left_upper:int)`` |->
            ``bounded_signed64_to_int (left_upper:bounded_signed64)``,
          ``(right_lower:int)`` |->
            ``bounded_signed64_to_int (right_lower:bounded_signed64)``,
          ``(right_upper:int)`` |->
            ``bounded_signed64_to_int (right_upper:bounded_signed64)``]
         bounded_object_int_product_extrema_mixed_mixed)
  >> impl_tac
  >- (fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> intLib.ARITH_TAC)
  >> strip_tac
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal left_lower right_upper`
  >> Cases_on
       `bounded_scaled_mul_floor64_decimal left_upper right_lower`
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal left_lower right_lower`
  >> Cases_on
       `bounded_scaled_mul_ceil64_decimal left_upper right_upper`
  >> gvs
       [compute_boundedIntervalDecimalTheory.bounded_interval64_product_mixed_decimal_def]
  >> rename1
       `bounded_scaled_mul_floor64_decimal left_lower right_upper =
          SOME rounded_lower_left`
  >> rename1
       `bounded_scaled_mul_floor64_decimal left_upper right_lower =
          SOME rounded_lower_right`
  >> rename1
       `bounded_scaled_mul_ceil64_decimal left_lower right_lower =
          SOME rounded_upper_left`
  >> rename1
       `bounded_scaled_mul_ceil64_decimal left_upper right_upper =
          SOME rounded_upper_right`
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_normalized
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_normalized
  >> Cases_on
       `bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_upper <=
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_lower`
  >> Cases_on
       `bounded_signed64_to_int left_lower *
          bounded_signed64_to_int right_lower <=
        bounded_signed64_to_int left_upper *
          bounded_signed64_to_int right_upper`
  >- (mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_lower_left`,
          `second_result` |-> `rounded_lower_right`]
         bounded_scaled_mul_floor64_decimal_cross_order)
      >> impl_tac
      >- simp []
      >> disch_tac
      >> mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_upper_left`,
          `second_result` |-> `rounded_upper_right`]
         bounded_scaled_mul_ceil64_decimal_same_sign_order)
      >> impl_tac
      >- simp []
      >> disch_tac
      >> fs
       [bounded_object_int_min_def,
        bounded_object_int_max_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_min_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_max_def,
        bounded_signed64_min_reverse_order,
        bounded_signed64_max_reverse_order]
      >> irule
       (Q.INST
         [`selected_lower_left` |-> `left_lower`,
          `selected_lower_right` |-> `right_upper`,
          `selected_upper_left` |-> `left_upper`,
          `selected_upper_right` |-> `right_upper`,
          `object_lower` |-> `object_lower`,
          `object_upper` |-> `object_upper`,
          `result` |->
            `BoundedInterval64 rounded_lower_left rounded_upper_right`]
         bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def])
  >- (mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_lower_left`,
          `second_result` |-> `rounded_lower_right`]
         bounded_scaled_mul_floor64_decimal_cross_order)
      >> impl_tac
      >- simp []
      >> disch_tac
      >> mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_upper_left`,
          `second_result` |-> `rounded_upper_right`]
         bounded_scaled_mul_ceil64_decimal_same_sign_reverse_order)
      >> impl_tac
      >- (simp [] >> intLib.ARITH_TAC)
      >> disch_tac
      >> `bounded_signed64_max rounded_upper_left rounded_upper_right =
            rounded_upper_left` by
           (irule bounded_signed64_max_reverse_order >> simp [])
      >> fs
       [bounded_object_int_min_def,
        bounded_object_int_max_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_min_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_max_def,
        bounded_signed64_min_reverse_order,
        bounded_signed64_max_reverse_order]
      >> irule
       (Q.INST
         [`selected_lower_left` |-> `left_lower`,
          `selected_lower_right` |-> `right_upper`,
          `selected_upper_left` |-> `left_lower`,
          `selected_upper_right` |-> `right_lower`,
          `object_lower` |-> `object_lower`,
          `object_upper` |-> `object_upper`,
          `result` |->
            `BoundedInterval64 rounded_lower_left rounded_upper_left`]
         bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def])
  >- (mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_lower_left`,
          `second_result` |-> `rounded_lower_right`]
         bounded_scaled_mul_floor64_decimal_cross_reverse_order)
      >> impl_tac
      >- (simp [] >> intLib.ARITH_TAC)
      >> disch_tac
      >> mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_upper_left`,
          `second_result` |-> `rounded_upper_right`]
         bounded_scaled_mul_ceil64_decimal_same_sign_order)
      >> impl_tac
      >- simp []
      >> disch_tac
      >> `bounded_signed64_min rounded_lower_left rounded_lower_right =
            rounded_lower_right` by
           (irule bounded_signed64_min_reverse_order >> simp [])
      >> fs
       [bounded_object_int_min_def,
        bounded_object_int_max_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_min_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_max_def,
        bounded_signed64_min_reverse_order,
        bounded_signed64_max_reverse_order]
      >> irule
       (Q.INST
         [`selected_lower_left` |-> `left_upper`,
          `selected_lower_right` |-> `right_lower`,
          `selected_upper_left` |-> `left_upper`,
          `selected_upper_right` |-> `right_upper`,
          `object_lower` |-> `object_lower`,
          `object_upper` |-> `object_upper`,
          `result` |->
            `BoundedInterval64 rounded_lower_right rounded_upper_right`]
         bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def])
  >> mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_lower_left`,
          `second_result` |-> `rounded_lower_right`]
         bounded_scaled_mul_floor64_decimal_cross_reverse_order)
  >> impl_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> disch_tac
  >> mp_tac
       (Q.INST
         [`negative_left` |-> `left_lower`,
          `positive_right` |-> `right_upper`,
          `positive_left` |-> `left_upper`,
          `negative_right` |-> `right_lower`,
          `first_result` |-> `rounded_upper_left`,
          `second_result` |-> `rounded_upper_right`]
         bounded_scaled_mul_ceil64_decimal_same_sign_reverse_order)
  >> impl_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> disch_tac
  >> `bounded_signed64_min rounded_lower_left rounded_lower_right =
        rounded_lower_right` by
       (irule bounded_signed64_min_reverse_order >> simp [])
  >> `bounded_signed64_max rounded_upper_left rounded_upper_right =
        rounded_upper_left` by
       (irule bounded_signed64_max_reverse_order >> simp [])
  >> fs
       [bounded_object_int_min_def,
        bounded_object_int_max_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_min_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_max_def,
        bounded_signed64_min_reverse_order,
        bounded_signed64_max_reverse_order]
  >> irule
       (Q.INST
         [`selected_lower_left` |-> `left_upper`,
          `selected_lower_right` |-> `right_lower`,
          `selected_upper_left` |-> `left_lower`,
          `selected_upper_right` |-> `right_lower`,
          `object_lower` |-> `object_lower`,
          `object_upper` |-> `object_upper`,
          `result` |->
            `BoundedInterval64 rounded_lower_right rounded_upper_left`]
         bounded_object_fs_interval_mul_decimal_from_pairs_exact)
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def]
QED

fun bounded_object_int_product_extrema_tac extrema_theorem =
  mp_tac
    (INST
      [``(left_lower:int)`` |->
         ``bounded_signed64_to_int (left_lower:bounded_signed64)``,
       ``(left_upper:int)`` |->
         ``bounded_signed64_to_int (left_upper:bounded_signed64)``,
       ``(right_lower:int)`` |->
         ``bounded_signed64_to_int (right_lower:bounded_signed64)``,
       ``(right_upper:int)`` |->
         ``bounded_signed64_to_int (right_upper:bounded_signed64)``]
      extrema_theorem)
  >> impl_tac
  >- intLib.ARITH_TAC
  >> strip_tac
  >> simp [];

Theorem bounded_object_fs_interval_mul_unchecked_decimal_components_exact:
  bounded_interval64_valid (BoundedInterval64 left_lower left_upper) /\
  bounded_interval64_valid (BoundedInterval64 right_lower right_upper) /\
  bounded_interval64_mul_unchecked_decimal
      (BoundedInterval64 left_lower left_upper)
      (BoundedInterval64 right_lower right_upper) = SOME result ==>
  bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv
        (BoundedInterval64 left_lower left_upper))
      (bounded_interval64_object_cv
        (BoundedInterval64 right_lower right_upper)) =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left_lower` |-> `left_lower`,
          `left_upper` |-> `left_upper`,
          `right_lower` |-> `right_lower`,
          `right_upper` |-> `right_upper`]
         bounded_object_fs_raw_interval_mul_object_cv_exists)
  >> disch_then
       (qx_choose_then `object_lower`
         (qx_choose_then `object_upper` assume_tac))
  >> Cases_on `bounded_signed64_nonnegative left_lower`
  >- (Cases_on `bounded_signed64_nonnegative right_lower`
      >- (fs
           [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
          >> irule
           (Q.INST
             [`selected_lower_left` |-> `left_lower`,
              `selected_lower_right` |-> `right_lower`,
              `selected_upper_left` |-> `left_upper`,
              `selected_upper_right` |-> `right_upper`,
              `object_lower` |-> `object_lower`,
              `object_upper` |-> `object_upper`,
              `result` |-> `result`]
             bounded_object_fs_interval_mul_decimal_from_pairs_exact)
          >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> bounded_object_int_product_extrema_tac
               bounded_object_int_product_extrema_nonnegative_nonnegative)
      >> Cases_on `bounded_signed64_nonpositive right_upper`
      >- (fs
           [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
          >> irule
           (Q.INST
             [`selected_lower_left` |-> `left_upper`,
              `selected_lower_right` |-> `right_lower`,
              `selected_upper_left` |-> `left_lower`,
              `selected_upper_right` |-> `right_upper`,
              `object_lower` |-> `object_lower`,
              `object_upper` |-> `object_upper`,
              `result` |-> `result`]
             bounded_object_fs_interval_mul_decimal_from_pairs_exact)
          >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> bounded_object_int_product_extrema_tac
               bounded_object_int_product_extrema_nonnegative_nonpositive)
      >> fs
           [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
      >> irule
           (Q.INST
             [`selected_lower_left` |-> `left_upper`,
              `selected_lower_right` |-> `right_lower`,
              `selected_upper_left` |-> `left_upper`,
              `selected_upper_right` |-> `right_upper`,
              `object_lower` |-> `object_lower`,
              `object_upper` |-> `object_upper`,
              `result` |-> `result`]
             bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> bounded_object_int_product_extrema_tac
           bounded_object_int_product_extrema_nonnegative_mixed)
  >> Cases_on `bounded_signed64_nonpositive left_upper`
  >- (Cases_on `bounded_signed64_nonnegative right_lower`
      >- (fs
           [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
          >> irule
           (Q.INST
             [`selected_lower_left` |-> `left_lower`,
              `selected_lower_right` |-> `right_upper`,
              `selected_upper_left` |-> `left_upper`,
              `selected_upper_right` |-> `right_lower`,
              `object_lower` |-> `object_lower`,
              `object_upper` |-> `object_upper`,
              `result` |-> `result`]
             bounded_object_fs_interval_mul_decimal_from_pairs_exact)
          >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> bounded_object_int_product_extrema_tac
               bounded_object_int_product_extrema_nonpositive_nonnegative)
      >> Cases_on `bounded_signed64_nonpositive right_upper`
      >- (fs
           [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
          >> irule
           (Q.INST
             [`selected_lower_left` |-> `left_upper`,
              `selected_lower_right` |-> `right_upper`,
              `selected_upper_left` |-> `left_lower`,
              `selected_upper_right` |-> `right_lower`,
              `object_lower` |-> `object_lower`,
              `object_upper` |-> `object_upper`,
              `result` |-> `result`]
             bounded_object_fs_interval_mul_decimal_from_pairs_exact)
          >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
          >> bounded_object_int_product_extrema_tac
               bounded_object_int_product_extrema_nonpositive_nonpositive)
      >> fs
           [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
      >> irule
           (Q.INST
             [`selected_lower_left` |-> `left_lower`,
              `selected_lower_right` |-> `right_upper`,
              `selected_upper_left` |-> `left_lower`,
              `selected_upper_right` |-> `right_lower`,
              `object_lower` |-> `object_lower`,
              `object_upper` |-> `object_upper`,
              `result` |-> `result`]
             bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
           [compute_boundedIntervalTheory.bounded_interval64_valid_def,
            compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
            compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> bounded_object_int_product_extrema_tac
           bounded_object_int_product_extrema_nonpositive_mixed)
  >> Cases_on `bounded_signed64_nonnegative right_lower`
  >- (fs
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
      >> irule
       (Q.INST
         [`selected_lower_left` |-> `left_lower`,
          `selected_lower_right` |-> `right_upper`,
          `selected_upper_left` |-> `left_upper`,
          `selected_upper_right` |-> `right_upper`,
          `object_lower` |-> `object_lower`,
          `object_upper` |-> `object_upper`,
          `result` |-> `result`]
         bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> bounded_object_int_product_extrema_tac
           bounded_object_int_product_extrema_mixed_nonnegative)
  >> Cases_on `bounded_signed64_nonpositive right_upper`
  >- (fs
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
      >> irule
       (Q.INST
         [`selected_lower_left` |-> `left_upper`,
          `selected_lower_right` |-> `right_lower`,
          `selected_upper_left` |-> `left_lower`,
          `selected_upper_right` |-> `right_lower`,
          `object_lower` |-> `object_lower`,
          `object_upper` |-> `object_upper`,
          `result` |-> `result`]
         bounded_object_fs_interval_mul_decimal_from_pairs_exact)
      >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
        compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct]
      >> bounded_object_int_product_extrema_tac
           bounded_object_int_product_extrema_mixed_nonpositive)
  >> fs
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def]
  >> irule bounded_object_fs_interval_mul_decimal_mixed_exact
  >> simp []
QED

Theorem bounded_object_fs_interval_mul_unchecked_decimal_exact:
  bounded_interval64_valid left /\
  bounded_interval64_valid right /\
  bounded_interval64_mul_unchecked_decimal left right = SOME result ==>
  bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) =
    SOME (bounded_interval64_object_cv result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> metis_tac
       [bounded_object_fs_interval_mul_unchecked_decimal_components_exact]
QED

Theorem bounded_object_fs_interval_mul_decimal_exact:
  bounded_interval64_mul_decimal left right = SOME result ==>
  bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> fs
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def]
  >> metis_tac
       [bounded_object_fs_interval_mul_unchecked_decimal_exact]
QED

val _ = export_theory ();
