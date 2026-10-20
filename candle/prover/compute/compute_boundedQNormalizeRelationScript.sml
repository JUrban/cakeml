(*****************************************************************************
 * Representation-independent rational normalization contract.
 *
 * The registered source normalizer may divide a signed numerator and its
 * positive denominator by a verified common factor, or fall back to the
 * unchanged representation.  The fast refinement must not depend on which
 * representation the bounded GCD search happens to select.  This theory
 * records the exact cross-multiplied rational relation preserved by either
 * branch.
 *****************************************************************************)
Theory compute_boundedQNormalizeRelation
Ancestors
  compute_boundedObjectIntervalRelation
Libs
  bossLib preamble intLib

Definition bounded_case10173_q_cv_equiv_def:
  bounded_case10173_q_cv_equiv left right <=>
    case bounded_object_q_ints left of
    | NONE => F
    | SOME (left_numerator,left_denominator) =>
      case bounded_object_q_ints right of
      | NONE => F
      | SOME (right_numerator,right_denominator) =>
          left_numerator * right_denominator =
            right_numerator * left_denominator
End

Definition bounded_case10173_lc_znormalize_cv_def:
  bounded_case10173_lc_znormalize_cv positive negative =
    if positive < negative then
      Pair (Num 0) (Num (negative - positive))
    else Pair (Num (positive - negative)) (Num 0)
End

Definition bounded_case10173_q_normalize_fallback_cv_def:
  bounded_case10173_q_normalize_fallback_cv signed denominator =
    Pair signed (Num (denominator - 1))
End

Definition bounded_case10173_q_normalize_divide_cv_def:
  bounded_case10173_q_normalize_divide_cv positive negative denominator
      common =
    Pair
      (Pair (Num (positive DIV common)) (Num (negative DIV common)))
      (Num (denominator DIV common - 1))
End

Definition bounded_case10173_q_normalize_verified_cv_def:
  bounded_case10173_q_normalize_verified_cv positive negative denominator
      common =
    if common = 0 then
      bounded_case10173_q_normalize_fallback_cv
        (Pair (Num positive) (Num negative)) denominator
    else if denominator DIV common = 0 then
      bounded_case10173_q_normalize_fallback_cv
        (Pair (Num positive) (Num negative)) denominator
    else if (positive DIV common) * common = positive then
      if (negative DIV common) * common = negative then
        if (denominator DIV common) * common = denominator then
          bounded_case10173_q_normalize_divide_cv
            positive negative denominator common
        else
          bounded_case10173_q_normalize_fallback_cv
            (Pair (Num positive) (Num negative)) denominator
      else
        bounded_case10173_q_normalize_fallback_cv
          (Pair (Num positive) (Num negative)) denominator
    else
      bounded_case10173_q_normalize_fallback_cv
        (Pair (Num positive) (Num negative)) denominator
End

Theorem bounded_case10173_q_cv_equiv_refl:
  bounded_object_q_ints value = SOME decoded ==>
  bounded_case10173_q_cv_equiv value value
Proof
  Cases_on `decoded`
  >> simp [bounded_case10173_q_cv_equiv_def]
QED

Theorem bounded_case10173_q_cv_equiv_trans:
  bounded_case10173_q_cv_equiv left middle /\
  bounded_case10173_q_cv_equiv middle right ==>
  bounded_case10173_q_cv_equiv left right
Proof
  rw [bounded_case10173_q_cv_equiv_def]
  >> every_case_tac
  >> gvs []
  >> `0 < r''` by
       metis_tac
         [compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive]
  >> `r'' <> 0` by intLib.ARITH_TAC
  >> `(q' * r) * r'' = (q * r') * r''` by
       metis_tac
         [integerTheory.INT_MUL_ASSOC,
          integerTheory.INT_MUL_COMM]
  >> metis_tac [integerTheory.INT_EQ_RMUL_IMP]
QED

Theorem bounded_case10173_int_signed_difference:
  positive < negative ==>
  -&(negative - positive) = (&positive:int) - &negative
Proof
  strip_tac
  >> (Q.SUBGOAL_THEN `positive <= negative` ASSUME_TAC THENL
       [DECIDE_TAC,
        ONCE_REWRITE_TAC [GSYM integerTheory.INT_NEG_SUB]
        >> simp [integerTheory.INT_SUB]])
QED

Theorem bounded_case10173_int_unsigned_difference:
  ~(positive < negative) ==>
  (&(positive - negative):int) = &positive - &negative
Proof
  strip_tac
  >> (Q.SUBGOAL_THEN `negative <= positive` ASSUME_TAC THENL
       [DECIDE_TAC,
        simp [integerTheory.INT_SUB]])
QED

Theorem bounded_case10173_suc_pred:
  0 < value ==> SUC (value - 1) = value
Proof
  DECIDE_TAC
QED

Theorem bounded_case10173_int_common_scale:
  common * positive' = positive /\
  common * negative' = negative /\
  common * denominator' = denominator ==>
  ((&positive':int) - &negative') * &denominator =
    (&positive - &negative) * &denominator'
Proof
  rpt strip_tac
  >> (`(&common:int) * &positive' = &positive` by
        simp [integerTheory.INT_MUL])
  >> (`(&common:int) * &negative' = &negative` by
        simp [integerTheory.INT_MUL])
  >> (`(&common:int) * &denominator' = &denominator` by
        simp [integerTheory.INT_MUL])
  >> qpat_x_assum `(&common:int) * &positive' = &positive`
       (fn th => ONCE_REWRITE_TAC [GSYM th])
  >> qpat_x_assum `(&common:int) * &negative' = &negative`
       (fn th => ONCE_REWRITE_TAC [GSYM th])
  >> qpat_x_assum `(&common:int) * &denominator' = &denominator`
       (fn th => ONCE_REWRITE_TAC [GSYM th])
  >> INT_RING_TAC
QED

Theorem bounded_case10173_lc_znormalize_cv_equiv:
  0 < denominator ==>
  bounded_case10173_q_cv_equiv
    (Pair (bounded_case10173_lc_znormalize_cv positive negative)
      (Num (denominator - 1)))
    (Pair (Pair (Num positive) (Num negative))
      (Num (denominator - 1)))
Proof
  rw [bounded_case10173_lc_znormalize_cv_def]
  >> simp
       [bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        bounded_case10173_int_signed_difference,
        bounded_case10173_int_unsigned_difference,
        integerTheory.INT_MUL, arithmeticTheory.MULT_COMM]
QED

Theorem bounded_case10173_q_normalize_verified_cv_equiv:
  0 < denominator ==>
  bounded_case10173_q_cv_equiv
    (bounded_case10173_q_normalize_verified_cv
      positive negative denominator common)
    (Pair (Pair (Num positive) (Num negative))
      (Num (denominator - 1)))
Proof
  rw
    [bounded_case10173_q_normalize_verified_cv_def,
     bounded_case10173_q_normalize_fallback_cv_def,
     bounded_case10173_q_normalize_divide_cv_def]
  >> simp
       [bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        bounded_case10173_suc_pred]
  >> (`(&common:int) * &(positive DIV common) = &positive` by
        simp [integerTheory.INT_MUL, arithmeticTheory.MULT_COMM])
  >> (`(&common:int) * &(negative DIV common) = &negative` by
        simp [integerTheory.INT_MUL, arithmeticTheory.MULT_COMM])
  >> (`(&common:int) * &(denominator DIV common) = &denominator` by
        simp [integerTheory.INT_MUL, arithmeticTheory.MULT_COMM])
  >> qpat_x_assum
       `(&common:int) * &(positive DIV common) = &positive`
       (fn th => ONCE_REWRITE_TAC [GSYM th])
  >> qpat_x_assum
       `(&common:int) * &(negative DIV common) = &negative`
       (fn th => ONCE_REWRITE_TAC [GSYM th])
  >> qpat_x_assum
       `(&common:int) * &(denominator DIV common) = &denominator`
       (fn th => ONCE_REWRITE_TAC [GSYM th])
  >> INT_RING_TAC
QED

val _ = export_theory ();
