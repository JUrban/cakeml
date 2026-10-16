(*****************************************************************************
 * Exact order bridge for the signed-pair representation used by the
 * authenticated decimal object checker.
 *
 * The object code compares a value [p - n] without first canonicalizing it:
 * [p1 + n2 < p2 + n1 + 1].  These lemmas connect that executable comparison,
 * and the derived min/max operations, to the normalized bounded carrier.
 *****************************************************************************)
Theory compute_boundedObjectDecimalOrder
Ancestors
  compute_boundedObjectDecimalArithmetic
Libs
  bossLib preamble intLib

Definition bounded_object_fs_raw_le_def:
  bounded_object_fs_raw_le
      (Pair (Num left_positive) (Num left_negative) : cv)
      (Pair (Num right_positive) (Num right_negative) : cv) =
    SOME
      (left_positive + right_negative <
       right_positive + left_negative + 1) /\
  bounded_object_fs_raw_le _ _ = NONE
End

Definition bounded_object_fs_raw_min_def:
  bounded_object_fs_raw_min left right =
    case bounded_object_fs_raw_le left right of
    | NONE => NONE
    | SOME left_le_right => SOME (if left_le_right then left else right)
End

Definition bounded_object_fs_raw_max_def:
  bounded_object_fs_raw_max left right =
    case bounded_object_fs_raw_le left right of
    | NONE => NONE
    | SOME left_le_right => SOME (if left_le_right then right else left)
End

Theorem bounded_object_fs_raw_le_signed_ints:
  bounded_object_signed_int left = SOME left_value /\
  bounded_object_signed_int right = SOME right_value ==>
  bounded_object_fs_raw_le left right = SOME (left_value <= right_value)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> gvs [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> rename1
       `bounded_object_signed_int (Pair left_first left_second) =
          SOME left_value`
  >> Cases_on `left_first`
  >> Cases_on `left_second`
  >> gvs [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> rename1
       `bounded_object_signed_int (Pair right_first right_second) =
          SOME right_value`
  >> Cases_on `right_first`
  >> Cases_on `right_second`
  >> gvs [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
          bounded_object_fs_raw_le_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_fs_raw_le_object_cv:
  bounded_object_fs_raw_le
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) =
    SOME (bounded_signed64_le left right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_object_fs_raw_le
          (bounded_signed64_object_cv (BoundedSigned64 left_negative left_word))
          (bounded_signed64_object_cv
            (BoundedSigned64 right_negative right_word)) = _`
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> Cases_on `left_word = 0w`
  >> Cases_on `right_word = 0w`
  >> simp [bounded_object_fs_raw_le_def,
           compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
           wordsTheory.WORD_LO,
           wordsTheory.w2n_eq_0]
  >> decide_tac
QED

Theorem bounded_object_fs_raw_min_object_cv:
  bounded_object_fs_raw_min
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) =
    SOME
      (bounded_signed64_object_cv
        (bounded_signed64_min left right))
Proof
  Cases_on `bounded_signed64_le left right`
  >> simp [bounded_object_fs_raw_min_def,
           bounded_object_fs_raw_le_object_cv,
           compute_boundedSignedEndpointTheory.bounded_signed64_min_def]
QED

Theorem bounded_object_fs_raw_max_object_cv:
  bounded_object_fs_raw_max
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) =
    SOME
      (bounded_signed64_object_cv
        (bounded_signed64_max left right))
Proof
  Cases_on `bounded_signed64_le left right`
  >> simp [bounded_object_fs_raw_max_def,
           bounded_object_fs_raw_le_object_cv,
           compute_boundedSignedEndpointTheory.bounded_signed64_max_def]
QED

Theorem bounded_object_fs_raw_mul_signed_value:
  bounded_object_fs_raw_mul
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) = SOME raw ==>
  bounded_object_signed_int raw =
    SOME
      (bounded_signed64_to_int left * bounded_signed64_to_int right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_object_fs_raw_mul
          (bounded_signed64_object_cv (BoundedSigned64 left_negative left_word))
          (bounded_signed64_object_cv
            (BoundedSigned64 right_negative right_word)) = SOME raw`
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> simp [compute_boundedObjectDecimalArithmeticTheory.bounded_object_fs_raw_mul_def,
           compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
           compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def]
  >> strip_tac
  >> gvs [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
