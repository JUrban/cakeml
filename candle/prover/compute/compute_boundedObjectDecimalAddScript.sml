(*****************************************************************************
 * Exact addition and negation bridge for the authenticated decimal object
 * checker.  The object program accumulates signed values as pairs of natural
 * numbers and canonicalizes only at the stored-interval boundary; the fast
 * checker uses normalized sign/magnitude words throughout.  These lemmas
 * prove that both representations produce the same ordinary cv values when
 * the checked word operation succeeds.
 *****************************************************************************)
Theory compute_boundedObjectDecimalAdd
Ancestors
  compute_boundedObjectDecimalArithmetic compute_boundedIntervalAdd
Libs
  bossLib preamble intLib

Definition bounded_object_fs_raw_add_def:
  bounded_object_fs_raw_add
      (Pair (Num left_positive) (Num left_negative) : cv)
      (Pair (Num right_positive) (Num right_negative) : cv) =
    SOME
      (Pair (Num (left_positive + right_positive))
        (Num (left_negative + right_negative))) /\
  bounded_object_fs_raw_add _ _ = NONE
End

Definition bounded_object_fs_raw_neg_def:
  bounded_object_fs_raw_neg
      (Pair (Num positive) (Num negative) : cv) =
    SOME (Pair (Num negative) (Num positive)) /\
  bounded_object_fs_raw_neg _ = NONE
End

Definition bounded_object_fs_canonical_def:
  bounded_object_fs_canonical
      (Pair (Num positive) (Num negative) : cv) =
    SOME
      (if positive < negative then
         Pair (Num 0) (Num (negative - positive))
       else
         Pair (Num (positive - negative)) (Num 0)) /\
  bounded_object_fs_canonical _ = NONE
End

Definition bounded_object_fs_add_def:
  bounded_object_fs_add left right =
    case bounded_object_fs_raw_add left right of
    | NONE => NONE
    | SOME raw => bounded_object_fs_canonical raw
End

Definition bounded_object_fs_neg_def:
  bounded_object_fs_neg value = bounded_object_fs_raw_neg value
End

Definition bounded_object_fs_interval_neg_def:
  bounded_object_fs_interval_neg (Pair lower upper : cv) =
    (case bounded_object_fs_neg upper of
     | NONE => NONE
     | SOME neg_upper =>
       case bounded_object_fs_neg lower of
       | NONE => NONE
       | SOME neg_lower => SOME (Pair neg_upper neg_lower)) /\
  bounded_object_fs_interval_neg _ = NONE
End

Definition bounded_object_fs_interval_add_def:
  bounded_object_fs_interval_add
      (Pair left_lower left_upper : cv)
      (Pair right_lower right_upper : cv) =
    (case bounded_object_fs_add left_lower right_lower of
     | NONE => NONE
     | SOME lower =>
       case bounded_object_fs_add left_upper right_upper of
       | NONE => NONE
       | SOME upper => SOME (Pair lower upper)) /\
  bounded_object_fs_interval_add _ _ = NONE
End

Definition bounded_object_fs_raw_interval_add_def:
  bounded_object_fs_raw_interval_add
      (Pair left_lower left_upper : cv)
      (Pair right_lower right_upper : cv) =
    (case bounded_object_fs_raw_add left_lower right_lower of
     | NONE => NONE
     | SOME lower =>
       case bounded_object_fs_raw_add left_upper right_upper of
       | NONE => NONE
       | SOME upper => SOME (Pair lower upper)) /\
  bounded_object_fs_raw_interval_add _ _ = NONE
End

Theorem bounded_object_fs_raw_add_signed_value:
  bounded_object_signed_int left = SOME left_value /\
  bounded_object_signed_int right = SOME right_value ==>
  ?raw.
    bounded_object_fs_raw_add left right = SOME raw /\
    bounded_object_signed_int raw = SOME (left_value + right_value)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> rename1
       `bounded_object_signed_int (Pair left_first left_second) =
          SOME left_value`
  >> Cases_on `left_first`
  >> Cases_on `left_second`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> rename1
       `bounded_object_signed_int (Pair right_first right_second) =
          SOME right_value`
  >> Cases_on `right_first`
  >> Cases_on `right_second`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        bounded_object_fs_raw_add_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_object_fs_raw_add_object_cv:
  ?raw.
    bounded_object_fs_raw_add
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) = SOME raw /\
    bounded_object_signed_int raw =
      SOME
        (bounded_signed64_to_int left + bounded_signed64_to_int right)
Proof
  match_mp_tac bounded_object_fs_raw_add_signed_value
  >> simp []
QED

Theorem bounded_object_fs_raw_neg_object_cv:
  bounded_object_fs_raw_neg (bounded_signed64_object_cv value) =
    SOME (bounded_signed64_object_cv (bounded_signed64_neg value))
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `magnitude = 0w`
  >> simp
       [bounded_object_fs_raw_neg_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        wordsTheory.w2n_eq_0]
QED

Theorem bounded_object_int_difference_nonnegative:
  (&positive:int) - &negative = &magnitude ==>
  ~(positive < negative) /\ positive - negative = magnitude
Proof
  intLib.ARITH_TAC
QED

Theorem bounded_object_int_difference_negative:
  0 < magnitude /\
  (&positive:int) - &negative = -&magnitude ==>
  positive < negative /\ negative - positive = magnitude
Proof
  intLib.ARITH_TAC
QED

Theorem bounded_object_fs_canonical_object_cv:
  bounded_object_signed_int raw =
      SOME (bounded_signed64_to_int result) /\
  bounded_signed64_normalized result ==>
  bounded_object_fs_canonical raw =
    SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `raw`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `c`
  >> Cases_on `c0`
  >> gvs
       [compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> Cases_on `result`
  >> Cases_on `b`
  >- (simp
       [bounded_object_fs_canonical_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def]
      >> strip_tac
      >> `0 < w2n c` by
           simp [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
                 wordsTheory.w2n_eq_0]
      >> imp_res_tac bounded_object_int_difference_negative
      >> simp [])
  >> simp
       [bounded_object_fs_canonical_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def]
  >> strip_tac
  >> imp_res_tac bounded_object_int_difference_nonnegative
  >> simp []
QED

Theorem bounded_object_fs_add_object_cv_exact:
  bounded_signed64_add left right = SOME result ==>
  bounded_object_fs_add
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) =
    SOME (bounded_signed64_object_cv result)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedSignedEndpointAddTheory.bounded_signed64_add_value
  >> mp_tac bounded_object_fs_raw_add_object_cv
  >> disch_then (qx_choose_then `raw` strip_assume_tac)
  >> imp_res_tac bounded_object_fs_canonical_object_cv
  >> simp [bounded_object_fs_add_def]
QED

Theorem bounded_object_fs_neg_object_cv_exact:
  bounded_object_fs_neg (bounded_signed64_object_cv value) =
    SOME (bounded_signed64_object_cv (bounded_signed64_neg value))
Proof
  simp [bounded_object_fs_neg_def, bounded_object_fs_raw_neg_object_cv]
QED

Theorem bounded_object_fs_interval_neg_object_cv_exact:
  bounded_object_fs_interval_neg (bounded_interval64_object_cv source) =
    SOME (bounded_interval64_object_cv (bounded_interval64_neg source))
Proof
  Cases_on `source`
  >> simp
       [bounded_object_fs_interval_neg_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        bounded_object_fs_neg_object_cv_exact]
QED

Theorem bounded_object_fs_interval_add_object_cv_exact:
  bounded_interval64_add left right = SOME result ==>
  bounded_object_fs_interval_add
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) =
    SOME (bounded_interval64_object_cv result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [compute_boundedIntervalAddTheory.bounded_interval64_add_def]
  >> fs [compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def]
  >> Cases_on `bounded_signed64_add b b'`
  >> gvs []
  >> Cases_on `bounded_signed64_add b0 b0'`
  >> gvs []
  >> simp
       [bounded_object_fs_interval_add_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> imp_res_tac bounded_object_fs_add_object_cv_exact
  >> simp []
QED

Theorem bounded_object_fs_raw_interval_add_object_cv:
  ?raw_lower raw_upper.
    bounded_object_fs_raw_interval_add
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) =
        SOME (Pair raw_lower raw_upper) /\
    bounded_object_signed_int raw_lower =
      SOME
        (bounded_signed64_to_int (bounded_interval64_lower left) +
         bounded_signed64_to_int (bounded_interval64_lower right)) /\
    bounded_object_signed_int raw_upper =
      SOME
        (bounded_signed64_to_int (bounded_interval64_upper left) +
         bounded_signed64_to_int (bounded_interval64_upper right))
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> mp_tac
       (Q.INST [`left` |-> `b`, `right` |-> `b'`]
          bounded_object_fs_raw_add_object_cv)
  >> disch_then (qx_choose_then `raw_lower` strip_assume_tac)
  >> mp_tac
       (Q.INST [`left` |-> `b0`, `right` |-> `b0'`]
          bounded_object_fs_raw_add_object_cv)
  >> disch_then (qx_choose_then `raw_upper` strip_assume_tac)
  >> qexists_tac `raw_lower`
  >> qexists_tac `raw_upper`
  >> fs
       [bounded_object_fs_raw_interval_add_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_object_fs_raw_interval_add_signed_values:
  bounded_object_signed_int left_lower = SOME left_lower_value /\
  bounded_object_signed_int left_upper = SOME left_upper_value /\
  bounded_object_signed_int right_lower = SOME right_lower_value /\
  bounded_object_signed_int right_upper = SOME right_upper_value ==>
  ?lower upper.
    bounded_object_fs_raw_interval_add
      (Pair left_lower left_upper)
      (Pair right_lower right_upper) = SOME (Pair lower upper) /\
    bounded_object_signed_int lower =
      SOME (left_lower_value + right_lower_value) /\
    bounded_object_signed_int upper =
      SOME (left_upper_value + right_upper_value)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `left_lower`, `right` |-> `right_lower`,
          `left_value` |-> `left_lower_value`,
          `right_value` |-> `right_lower_value`]
         bounded_object_fs_raw_add_signed_value)
  >> simp []
  >> disch_then (qx_choose_then `lower` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`left` |-> `left_upper`, `right` |-> `right_upper`,
          `left_value` |-> `left_upper_value`,
          `right_value` |-> `right_upper_value`]
         bounded_object_fs_raw_add_signed_value)
  >> simp []
  >> disch_then (qx_choose_then `upper` strip_assume_tac)
  >> qexists_tac `lower`
  >> qexists_tac `upper`
  >> simp [bounded_object_fs_raw_interval_add_def]
QED

val _ = export_theory ();
