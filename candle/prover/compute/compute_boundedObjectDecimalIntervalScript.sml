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

val _ = export_theory ();
