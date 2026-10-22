(*****************************************************************************
 * Small algebraic closure lemmas for the representation-independent rational
 * relation used by the registered nonlinear evaluator refinements.
 *****************************************************************************)
Theory compute_boundedQRelationAlgebra
Ancestors
  compute_boundedQNormalizeRelation
Libs
  bossLib preamble intLib

Theorem bounded_case10173_q_cv_equiv_sym:
  bounded_case10173_q_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv right left
Proof
  rw
    [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_case10173_positive_q_add_cv_equiv:
  0 < left_denominator /\ 0 < right_denominator /\
  0 < left_denominator' /\ 0 < right_denominator' /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1)))
    (Pair (Pair (Num left_numerator') (Num 0))
      (Num (left_denominator' - 1))) /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1)))
    (Pair (Pair (Num right_numerator') (Num 0))
      (Num (right_denominator' - 1))) ==>
  bounded_case10173_q_cv_equiv
    (Pair
      (Pair
        (Num
          (left_numerator * right_denominator +
           right_numerator * left_denominator))
        (Num 0))
      (Num (left_denominator * right_denominator - 1)))
    (Pair
      (Pair
        (Num
          (left_numerator' * right_denominator' +
           right_numerator' * left_denominator'))
        (Num 0))
      (Num (left_denominator' * right_denominator' - 1)))
Proof
  strip_tac
  >> `SUC (left_denominator - 1) = left_denominator` by intLib.ARITH_TAC
  >> `SUC (right_denominator - 1) = right_denominator` by intLib.ARITH_TAC
  >> `SUC (left_denominator' - 1) = left_denominator'` by intLib.ARITH_TAC
  >> `SUC (right_denominator' - 1) = right_denominator'` by intLib.ARITH_TAC
  >> `SUC (left_denominator * right_denominator - 1) =
      left_denominator * right_denominator` by
       (irule compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> metis_tac [arithmeticTheory.MULT_POS])
  >> `SUC (left_denominator' * right_denominator' - 1) =
      left_denominator' * right_denominator'` by
       (irule compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> metis_tac [arithmeticTheory.MULT_POS])
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_MUL]
  >> `left_denominator' * right_denominator' *
        (left_denominator * right_numerator) =
      left_denominator * right_denominator *
        (left_denominator' * right_numerator')` by
       metis_tac [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM]
  >> `left_denominator' * right_denominator' *
        (left_numerator * right_denominator) =
      left_denominator * right_denominator *
        (left_numerator' * right_denominator')` by
       metis_tac [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case10173_positive_q_inv_cv_equiv:
  0 < left_numerator /\ 0 < left_denominator /\
  0 < right_numerator /\ 0 < right_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1)))
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1))) ==>
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_denominator) (Num 0))
      (Num (left_numerator - 1)))
    (Pair (Pair (Num right_denominator) (Num 0))
      (Num (right_numerator - 1)))
Proof
  strip_tac
  >> `SUC (left_denominator - 1) = left_denominator` by intLib.ARITH_TAC
  >> `SUC (right_denominator - 1) = right_denominator` by intLib.ARITH_TAC
  >> `SUC (left_numerator - 1) = left_numerator` by intLib.ARITH_TAC
  >> `SUC (right_numerator - 1) = right_numerator` by intLib.ARITH_TAC
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_MUL]
  >> metis_tac [arithmeticTheory.MULT_COMM]
QED

val _ = export_theory ();
