(*****************************************************************************
 * Rational-equivalence preservation of positive endpoint order.
 *
 * Normalization changes numerators and denominators but not represented
 * rationals.  This lemma transports an interval endpoint order through that
 * representation change, allowing the generic four-product selector to be
 * specialized only after the source intervals have been authenticated.
 *****************************************************************************)
Theory compute_registeredCase10173PositiveIntervalOrderEquiv
Ancestors
  compute_registeredCase10173PositiveIntervalOrder
  compute_registeredCase10173QDecimalEquiv
Libs
  bossLib preamble intLib

Theorem registered_case10173_positive_q_order_equiv:
  0 < left_lower_denominator /\ 0 < left_upper_denominator /\
  0 < right_lower_denominator /\ 0 < right_upper_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_lower) (Num 0))
      (Num (left_lower_denominator - 1)))
    (Pair (Pair (Num right_lower) (Num 0))
      (Num (right_lower_denominator - 1))) /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_upper) (Num 0))
      (Num (left_upper_denominator - 1)))
    (Pair (Pair (Num right_upper) (Num 0))
      (Num (right_upper_denominator - 1))) /\
  right_lower * right_upper_denominator <=
    right_upper * right_lower_denominator ==>
  left_lower * left_upper_denominator <=
    left_upper * left_lower_denominator
Proof
  strip_tac
  >> `left_lower * right_lower_denominator =
      right_lower * left_lower_denominator` by
       (irule
          compute_registeredCase10173QDecimalEquivTheory.registered_case10173_positive_q_cv_equiv_cross
        >> asm_rewrite_tac [])
  >> `left_upper * right_upper_denominator =
      right_upper * left_upper_denominator` by
       (irule
          compute_registeredCase10173QDecimalEquivTheory.registered_case10173_positive_q_cv_equiv_cross
        >> asm_rewrite_tac [])
  >> `(left_lower_denominator * left_upper_denominator) *
        (right_lower * right_upper_denominator) <=
      (left_lower_denominator * left_upper_denominator) *
        (right_upper * right_lower_denominator)` by
       simp [arithmeticTheory.LE_MULT_LCANCEL]
  >> `(left_lower * left_upper_denominator) *
        (right_lower_denominator * right_upper_denominator) <=
      (left_upper * left_lower_denominator) *
        (right_lower_denominator * right_upper_denominator)` by
       metis_tac [arithmeticTheory.MULT_ASSOC, arithmeticTheory.MULT_COMM]
  >> qpat_x_assum
       `(left_lower * left_upper_denominator) * _ <= _`
       mp_tac
  >> simp [arithmeticTheory.LE_MULT_RCANCEL,
           arithmeticTheory.MULT_POS]
QED

Theorem registered_case10173_positive_q_self_add_order:
  (lower:num) * upper_denominator <= upper * lower_denominator ==>
  (lower * lower_denominator + lower * lower_denominator) *
      (upper_denominator * upper_denominator) <=
    (upper * upper_denominator + upper * upper_denominator) *
      (lower_denominator * lower_denominator)
Proof
  strip_tac
  >> qpat_x_assum
       `lower * upper_denominator <= upper * lower_denominator`
       (fn order =>
          let
            val product_order =
              MATCH_MP
                (Q.INST
                  [`a` |-> `lower`, `d` |-> `upper_denominator`,
                   `b` |-> `upper`, `c` |-> `lower_denominator`,
                   `x` |-> `2 * lower_denominator`,
                   `y` |-> `upper_denominator`]
                  compute_registeredCase10173PositiveIntervalOrderTheory.registered_case10173_cross_product_le)
                order
            val left_eq =
              Grobner.NUM_RING
                ``(((2 * lower_denominator) * (lower:num)) *
                     (upper_denominator * upper_denominator) =
                   (lower * lower_denominator +
                    lower * lower_denominator) *
                     (upper_denominator * upper_denominator)):bool``
            val right_eq =
              Grobner.NUM_RING
                ``(((2 * lower_denominator) * (upper:num)) *
                     (upper_denominator * lower_denominator) =
                   (upper * upper_denominator +
                    upper * upper_denominator) *
                     (lower_denominator * lower_denominator)):bool``
            val proposition_eq =
              MK_COMB
                (AP_TERM (rator (rator (concl product_order))) left_eq,
                 right_eq)
          in
            ACCEPT_TAC (EQ_MP proposition_eq product_order)
          end)
QED

val _ = export_theory ();
