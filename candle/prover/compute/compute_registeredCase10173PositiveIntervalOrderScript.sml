(*****************************************************************************
 * Ordered positive rational interval products.
 *
 * The generic source multiplier takes min/max over four endpoint products.
 * For the authenticated square-root and source-box intervals both inputs are
 * positive and ordered, so the selected endpoints are the lower/lower and
 * upper/upper products.  Keeping this algebra separate avoids baking that
 * special case into the evaluator implementation.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalOrder
Ancestors
  compute_registeredCase10173PositiveIntervalMulEval
  compute_boundedQRelationAlgebra
Libs
  bossLib preamble intLib

Theorem registered_case10173_cross_product_le:
  (a:num) * d <= b * c ==>
  (x * a) * (y * d) <= (x * b) * (y * c)
Proof
  strip_tac
  >> `(a * d) * (x * y) <= (b * c) * (x * y)` by
       metis_tac [arithmeticTheory.LESS_MONO_MULT]
  >> metis_tac [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_positive_q_mul_cv_equiv:
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
    (Pair (Pair (Num (left_numerator * right_numerator)) (Num 0))
      (Num (left_denominator * right_denominator - 1)))
    (Pair (Pair (Num (left_numerator' * right_numerator')) (Num 0))
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
  >> metis_tac [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_q_minmax_ordered:
  left_value * right_denominator <= right_value * left_denominator ==>
  registered_case10173_q_min_value
      left_value left_denominator right_value right_denominator =
    left_value /\
  registered_case10173_q_min_denominator
      left_value left_denominator right_value right_denominator =
    left_denominator /\
  registered_case10173_q_max_value
      left_value left_denominator right_value right_denominator =
    right_value /\
  registered_case10173_q_max_denominator
      left_value left_denominator right_value right_denominator =
    right_denominator
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min_value_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min_denominator_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max_value_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max_denominator_def]
QED

Theorem registered_case10173_q_minmax4_ordered:
  a_value * b_denominator <= b_value * a_denominator /\
  c_value * d_denominator <= d_value * c_denominator /\
  a_value * c_denominator <= c_value * a_denominator /\
  b_value * d_denominator <= d_value * b_denominator ==>
  registered_case10173_q_min4_value
      a_value a_denominator b_value b_denominator
      c_value c_denominator d_value d_denominator = a_value /\
  registered_case10173_q_min4_denominator
      a_value a_denominator b_value b_denominator
      c_value c_denominator d_value d_denominator = a_denominator /\
  registered_case10173_q_max4_value
      a_value a_denominator b_value b_denominator
      c_value c_denominator d_value d_denominator = d_value /\
  registered_case10173_q_max4_denominator
      a_value a_denominator b_value b_denominator
      c_value c_denominator d_value d_denominator = d_denominator
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min4_value_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min4_denominator_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max4_value_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max4_denominator_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min_value_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_min_denominator_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max_value_def,
        compute_registeredCase10173PositiveIntervalMulEvalTheory.registered_case10173_q_max_denominator_def]
QED

Theorem registered_case10173_product_lower_y_order:
  (y_lower:num) * y_upper_denominator <=
    y_upper * y_lower_denominator ==>
  (x_lower * y_lower) *
      (x_lower_denominator * y_upper_denominator) <=
    (x_lower * y_upper) *
      (x_lower_denominator * y_lower_denominator)
Proof
  strip_tac
  >> irule
       (Q.INST
         [`a` |-> `y_lower`, `d` |-> `y_upper_denominator`,
          `b` |-> `y_upper`, `c` |-> `y_lower_denominator`,
          `x` |-> `x_lower`, `y` |-> `x_lower_denominator`]
         registered_case10173_cross_product_le)
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_product_upper_y_order:
  (y_lower:num) * y_upper_denominator <=
    y_upper * y_lower_denominator ==>
  (x_upper * y_lower) *
      (x_upper_denominator * y_upper_denominator) <=
    (x_upper * y_upper) *
      (x_upper_denominator * y_lower_denominator)
Proof
  strip_tac
  >> irule
       (Q.INST
         [`a` |-> `y_lower`, `d` |-> `y_upper_denominator`,
          `b` |-> `y_upper`, `c` |-> `y_lower_denominator`,
          `x` |-> `x_upper`, `y` |-> `x_upper_denominator`]
         registered_case10173_cross_product_le)
  >> first_assum ACCEPT_TAC
QED

Theorem registered_case10173_product_lower_x_order:
  (x_lower:num) * x_upper_denominator <=
    x_upper * x_lower_denominator ==>
  (x_lower * y_lower) *
      (x_upper_denominator * y_lower_denominator) <=
    (x_upper * y_lower) *
      (x_lower_denominator * y_lower_denominator)
Proof
  strip_tac
  >> qpat_x_assum
       `x_lower * x_upper_denominator <=
        x_upper * x_lower_denominator`
       (fn order =>
          let
            val product_order =
              MATCH_MP
                (Q.INST
                  [`a` |-> `x_lower`, `d` |-> `x_upper_denominator`,
                   `b` |-> `x_upper`, `c` |-> `x_lower_denominator`,
                   `x` |-> `y_lower`, `y` |-> `y_lower_denominator`]
                  registered_case10173_cross_product_le)
                order
            val left_eq =
              EQT_ELIM
                (AC_CONV
                  (arithmeticTheory.MULT_ASSOC,
                   arithmeticTheory.MULT_COMM)
                  ``((y_lower:num) * x_lower) *
                      (y_lower_denominator * x_upper_denominator) =
                    (x_lower * y_lower) *
                      (x_upper_denominator * y_lower_denominator)``)
            val right_eq =
              EQT_ELIM
                (AC_CONV
                  (arithmeticTheory.MULT_ASSOC,
                   arithmeticTheory.MULT_COMM)
                  ``((y_lower:num) * x_upper) *
                      (y_lower_denominator * x_lower_denominator) =
                    (x_upper * y_lower) *
                      (x_lower_denominator * y_lower_denominator)``)
            val proposition_eq =
              MK_COMB
                (AP_TERM (rator (rator (concl product_order))) left_eq,
                 right_eq)
          in
            ACCEPT_TAC (EQ_MP proposition_eq product_order)
          end)
QED

Theorem registered_case10173_product_upper_x_order:
  (x_lower:num) * x_upper_denominator <=
    x_upper * x_lower_denominator ==>
  (x_lower * y_upper) *
      (x_upper_denominator * y_upper_denominator) <=
    (x_upper * y_upper) *
      (x_lower_denominator * y_upper_denominator)
Proof
  strip_tac
  >> qpat_x_assum
       `x_lower * x_upper_denominator <=
        x_upper * x_lower_denominator`
       (fn order =>
          let
            val product_order =
              MATCH_MP
                (Q.INST
                  [`a` |-> `x_lower`, `d` |-> `x_upper_denominator`,
                   `b` |-> `x_upper`, `c` |-> `x_lower_denominator`,
                   `x` |-> `y_upper`, `y` |-> `y_upper_denominator`]
                  registered_case10173_cross_product_le)
                order
            val left_eq =
              EQT_ELIM
                (AC_CONV
                  (arithmeticTheory.MULT_ASSOC,
                   arithmeticTheory.MULT_COMM)
                  ``((y_upper:num) * x_lower) *
                      (y_upper_denominator * x_upper_denominator) =
                    (x_lower * y_upper) *
                      (x_upper_denominator * y_upper_denominator)``)
            val right_eq =
              EQT_ELIM
                (AC_CONV
                  (arithmeticTheory.MULT_ASSOC,
                   arithmeticTheory.MULT_COMM)
                  ``((y_upper:num) * x_upper) *
                      (y_upper_denominator * x_lower_denominator) =
                    (x_upper * y_upper) *
                      (x_lower_denominator * y_upper_denominator)``)
            val proposition_eq =
              MK_COMB
                (AP_TERM (rator (rator (concl product_order))) left_eq,
                 right_eq)
          in
            ACCEPT_TAC (EQ_MP proposition_eq product_order)
          end)
QED

Theorem registered_case10173_q_minmax4_ordered_positive_products:
  x_lower * x_upper_denominator <=
    x_upper * x_lower_denominator /\
  y_lower * y_upper_denominator <=
    y_upper * y_lower_denominator ==>
  registered_case10173_q_min4_value
      (x_lower * y_lower)
        (x_lower_denominator * y_lower_denominator)
      (x_lower * y_upper)
        (x_lower_denominator * y_upper_denominator)
      (x_upper * y_lower)
        (x_upper_denominator * y_lower_denominator)
      (x_upper * y_upper)
        (x_upper_denominator * y_upper_denominator) =
    x_lower * y_lower /\
  registered_case10173_q_min4_denominator
      (x_lower * y_lower)
        (x_lower_denominator * y_lower_denominator)
      (x_lower * y_upper)
        (x_lower_denominator * y_upper_denominator)
      (x_upper * y_lower)
        (x_upper_denominator * y_lower_denominator)
      (x_upper * y_upper)
        (x_upper_denominator * y_upper_denominator) =
    x_lower_denominator * y_lower_denominator /\
  registered_case10173_q_max4_value
      (x_lower * y_lower)
        (x_lower_denominator * y_lower_denominator)
      (x_lower * y_upper)
        (x_lower_denominator * y_upper_denominator)
      (x_upper * y_lower)
        (x_upper_denominator * y_lower_denominator)
      (x_upper * y_upper)
        (x_upper_denominator * y_upper_denominator) =
    x_upper * y_upper /\
  registered_case10173_q_max4_denominator
      (x_lower * y_lower)
        (x_lower_denominator * y_lower_denominator)
      (x_lower * y_upper)
        (x_lower_denominator * y_upper_denominator)
      (x_upper * y_lower)
        (x_upper_denominator * y_lower_denominator)
      (x_upper * y_upper)
        (x_upper_denominator * y_upper_denominator) =
    x_upper_denominator * y_upper_denominator
Proof
  strip_tac
  >> irule registered_case10173_q_minmax4_ordered
  >> rpt conj_tac
  >- (irule registered_case10173_product_lower_y_order
      >> first_assum ACCEPT_TAC)
  >- (irule registered_case10173_product_lower_x_order
      >> first_assum ACCEPT_TAC)
  >- (irule registered_case10173_product_upper_x_order
      >> first_assum ACCEPT_TAC)
  >> irule registered_case10173_product_upper_y_order
  >> first_assum ACCEPT_TAC
QED

val _ = export_theory ();
