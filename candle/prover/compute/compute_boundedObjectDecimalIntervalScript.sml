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
  bossLib preamble

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
