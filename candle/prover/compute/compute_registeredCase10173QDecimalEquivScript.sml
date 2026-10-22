(*****************************************************************************
 * Decimal conversion is invariant under positive rational normalization.
 *
 * The unchanged source normalizer may choose any verified common divisor.
 * Later square-root refinements must therefore depend on the represented
 * rational, not on the selected numerator/denominator pair.  This file
 * proves that outward scale-10^12 conversion is identical for two positive
 * encodings related by the normalization contract.
 *****************************************************************************)
Theory compute_registeredCase10173QDecimalEquiv
Ancestors
  compute_registeredCase10173QNormalizeRelationEval
  compute_boundedObjectDecimalQ
Libs
  bossLib preamble intLib

Theorem registered_case10173_scaled_fraction_floor_eq:
  0 < left_denominator /\ 0 < right_denominator /\
  left_numerator * right_denominator =
    right_numerator * left_denominator ==>
  scale * left_numerator DIV left_denominator =
    scale * right_numerator DIV right_denominator
Proof
  strip_tac
  >> qabbrev_tac
       `quotient = scale * left_numerator DIV left_denominator`
  >> `quotient * left_denominator <= scale * left_numerator /\
      scale * left_numerator < SUC quotient * left_denominator` by
       (irule
          (iffLR
            (Q.SPECL
              [`quotient`,`scale * left_numerator`,`left_denominator`]
              arithmeticTheory.DIV_EQ_X))
        >> asm_rewrite_tac []
        >> qunabbrev_tac `quotient`
        >> simp [])
  >> `scale * (left_numerator * right_denominator) =
      scale * (right_numerator * left_denominator)` by
       asm_rewrite_tac []
  >> `(scale * left_numerator) * right_denominator =
      (scale * right_numerator) * left_denominator` by
       (rewrite_tac [GSYM arithmeticTheory.MULT_ASSOC]
        >> asm_rewrite_tac [])
  >> `(quotient * left_denominator) * right_denominator <=
      (scale * left_numerator) * right_denominator` by
       (irule
          (iffRL
            (Q.SPECL
              [`quotient * left_denominator`,`right_denominator`,
               `scale * left_numerator`]
              arithmeticTheory.LE_MULT_RCANCEL))
        >> asm_rewrite_tac []
        >> simp [])
  >> `(quotient * right_denominator) * left_denominator =
      (quotient * left_denominator) * right_denominator` by
       CONV_TAC
         (AC_CONV
           (arithmeticTheory.MULT_ASSOC,arithmeticTheory.MULT_COMM))
  >> `(quotient * right_denominator) * left_denominator <=
      (scale * right_numerator) * left_denominator` by
       metis_tac []
  >> `left_denominator <> 0` by intLib.ARITH_TAC
  >> `quotient * right_denominator <= scale * right_numerator` by
       (qpat_x_assum
          `(quotient * right_denominator) * left_denominator <= _`
          mp_tac
        >> simp [arithmeticTheory.LE_MULT_RCANCEL])
  >> `(scale * left_numerator) * right_denominator <
      (SUC quotient * left_denominator) * right_denominator` by
       (irule
          (iffRL
            (Q.SPECL
              [`scale * left_numerator`,`right_denominator`,
               `SUC quotient * left_denominator`]
              arithmeticTheory.LT_MULT_RCANCEL))
        >> asm_rewrite_tac [])
  >> `(SUC quotient * right_denominator) * left_denominator =
      (SUC quotient * left_denominator) * right_denominator` by
       CONV_TAC
         (AC_CONV
           (arithmeticTheory.MULT_ASSOC,arithmeticTheory.MULT_COMM))
  >> `(scale * right_numerator) * left_denominator <
      (SUC quotient * right_denominator) * left_denominator` by
       metis_tac []
  >> `scale * right_numerator <
      SUC quotient * right_denominator` by
       (qpat_x_assum
          `(scale * right_numerator) * left_denominator < _`
          mp_tac
        >> simp [arithmeticTheory.LT_MULT_RCANCEL])
  >> irule EQ_SYM
  >> irule
       (iffRL
         (Q.SPECL
           [`quotient`,`scale * right_numerator`,`right_denominator`]
           arithmeticTheory.DIV_EQ_X))
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_scaled_fraction_mod_zero_eq:
  0 < left_denominator /\ 0 < right_denominator /\
  left_numerator * right_denominator =
    right_numerator * left_denominator ==>
  (scale * left_numerator MOD left_denominator = 0 <=>
   scale * right_numerator MOD right_denominator = 0)
Proof
  strip_tac
  >> `scale * left_numerator DIV left_denominator =
      scale * right_numerator DIV right_denominator` by
       metis_tac [registered_case10173_scaled_fraction_floor_eq]
  >> qabbrev_tac
       `quotient = scale * left_numerator DIV left_denominator`
  >> `(scale * left_numerator) * right_denominator =
      (scale * right_numerator) * left_denominator` by
       (rewrite_tac [GSYM arithmeticTheory.MULT_ASSOC]
        >> asm_rewrite_tac [])
  >> `(quotient * right_denominator) * left_denominator =
      (quotient * left_denominator) * right_denominator` by
       CONV_TAC
         (AC_CONV
           (arithmeticTheory.MULT_ASSOC,arithmeticTheory.MULT_COMM))
  >> eq_tac
  >> strip_tac
  >- (`scale * left_numerator = quotient * left_denominator` by
        (mp_tac (Q.SPEC `left_denominator` arithmeticTheory.DIVISION)
         >> asm_rewrite_tac []
         >> disch_then (qspec_then `scale * left_numerator` mp_tac)
         >> qunabbrev_tac `quotient`
         >> asm_rewrite_tac []
         >> simp [])
      >> `(scale * right_numerator) * left_denominator =
          (quotient * right_denominator) * left_denominator` by
           metis_tac []
      >> `left_denominator <> 0` by intLib.ARITH_TAC
      >> `left_denominator = 0 \/
          scale * right_numerator = quotient * right_denominator` by
           (irule
              (iffLR
                (Q.SPECL
                  [`left_denominator`,`scale * right_numerator`,
                   `quotient * right_denominator`]
                  arithmeticTheory.EQ_MULT_RCANCEL))
            >> qpat_x_assum
                 `(scale * right_numerator) * left_denominator =
                  (quotient * right_denominator) * left_denominator`
                 (fn th => ACCEPT_TAC th))
      >> `scale * right_numerator = quotient * right_denominator` by
           metis_tac []
      >> qpat_x_assum
           `scale * right_numerator = quotient * right_denominator`
           (fn th => once_rewrite_tac [th])
      >> irule arithmeticTheory.MOD_EQ_0
      >> asm_rewrite_tac [])
  >> `scale * right_numerator = quotient * right_denominator` by
       (mp_tac (Q.SPEC `right_denominator` arithmeticTheory.DIVISION)
        >> asm_rewrite_tac []
        >> disch_then (qspec_then `scale * right_numerator` mp_tac)
        >> asm_rewrite_tac []
        >> simp [])
  >> `(scale * left_numerator) * right_denominator =
      (quotient * left_denominator) * right_denominator` by
       metis_tac []
  >> `right_denominator <> 0` by intLib.ARITH_TAC
  >> `right_denominator = 0 \/
      scale * left_numerator = quotient * left_denominator` by
       (irule
          (iffLR
            (Q.SPECL
              [`right_denominator`,`scale * left_numerator`,
               `quotient * left_denominator`]
              arithmeticTheory.EQ_MULT_RCANCEL))
        >> qpat_x_assum
             `(scale * left_numerator) * right_denominator =
              (quotient * left_denominator) * right_denominator`
             (fn th => ACCEPT_TAC th))
  >> `scale * left_numerator = quotient * left_denominator` by
       metis_tac []
  >> qpat_x_assum
       `scale * left_numerator = quotient * left_denominator`
       (fn th => once_rewrite_tac [th])
  >> irule arithmeticTheory.MOD_EQ_0
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_scaled_fraction_ceil_eq:
  0 < left_denominator /\ 0 < right_denominator /\
  left_numerator * right_denominator =
    right_numerator * left_denominator ==>
  scale * left_numerator DIV left_denominator +
      (if scale * left_numerator MOD left_denominator = 0 then 0 else 1) =
    scale * right_numerator DIV right_denominator +
      (if scale * right_numerator MOD right_denominator = 0 then 0 else 1)
Proof
  strip_tac
  >> `scale * left_numerator DIV left_denominator =
      scale * right_numerator DIV right_denominator` by
       (irule registered_case10173_scaled_fraction_floor_eq
        >> asm_rewrite_tac [])
  >> `(scale * left_numerator MOD left_denominator = 0 <=>
       scale * right_numerator MOD right_denominator = 0)` by
       (irule registered_case10173_scaled_fraction_mod_zero_eq
        >> asm_rewrite_tac [])
  >> Cases_on `scale * left_numerator MOD left_denominator = 0`
  >> fs []
QED

Theorem registered_case10173_positive_q_cv_equiv_cross:
  0 < left_denominator /\ 0 < right_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1)))
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1))) ==>
  left_numerator * right_denominator =
    right_numerator * left_denominator
Proof
  strip_tac
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def,
        integerTheory.INT_MUL]
  >> `SUC (left_denominator - 1) = left_denominator` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> asm_rewrite_tac [])
  >> `SUC (right_denominator - 1) = right_denominator` by
       (irule
          compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred
        >> asm_rewrite_tac [])
  >> fs [arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_positive_q_floor64_decimal_equiv:
  0 < left_numerator /\ 0 < left_denominator /\
  0 < right_numerator /\ 0 < right_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1)))
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1))) ==>
  bounded_object_positive_q_floor64_decimal
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1))) =
  bounded_object_positive_q_floor64_decimal
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1)))
Proof
  strip_tac
  >> `left_numerator * right_denominator =
      right_numerator * left_denominator` by
       (irule registered_case10173_positive_q_cv_equiv_cross
        >> asm_rewrite_tac [])
  >> `1000000000000 * left_numerator DIV left_denominator =
      1000000000000 * right_numerator DIV right_denominator` by
       (irule registered_case10173_scaled_fraction_floor_eq
        >> asm_rewrite_tac [])
  >> simp
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def,
        compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred]
QED

Theorem registered_case10173_positive_q_ceil64_decimal_equiv:
  0 < left_numerator /\ 0 < left_denominator /\
  0 < right_numerator /\ 0 < right_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1)))
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1))) ==>
  bounded_object_positive_q_ceil64_decimal
    (Pair (Pair (Num left_numerator) (Num 0))
      (Num (left_denominator - 1))) =
  bounded_object_positive_q_ceil64_decimal
    (Pair (Pair (Num right_numerator) (Num 0))
      (Num (right_denominator - 1)))
Proof
  strip_tac
  >> `left_numerator * right_denominator =
      right_numerator * left_denominator` by
       (irule registered_case10173_positive_q_cv_equiv_cross
        >> asm_rewrite_tac [])
  >> `1000000000000 * left_numerator DIV left_denominator +
        (if 1000000000000 * left_numerator MOD left_denominator = 0
         then 0 else 1) =
      1000000000000 * right_numerator DIV right_denominator +
        (if 1000000000000 * right_numerator MOD right_denominator = 0
         then 0 else 1)` by
       (irule registered_case10173_scaled_fraction_ceil_eq
        >> asm_rewrite_tac [])
  >> simp
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def,
        compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_suc_pred,
        compute_boundedSignedTheory.bounded_div_ceil]
QED

Theorem registered_case10173_positive_q_interval64_decimal_equiv:
  0 < left_lower /\ 0 < left_lower_denominator /\
  0 < right_lower /\ 0 < right_lower_denominator /\
  0 < left_upper /\ 0 < left_upper_denominator /\
  0 < right_upper /\ 0 < right_upper_denominator /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_lower) (Num 0))
      (Num (left_lower_denominator - 1)))
    (Pair (Pair (Num right_lower) (Num 0))
      (Num (right_lower_denominator - 1))) /\
  bounded_case10173_q_cv_equiv
    (Pair (Pair (Num left_upper) (Num 0))
      (Num (left_upper_denominator - 1)))
    (Pair (Pair (Num right_upper) (Num 0))
      (Num (right_upper_denominator - 1))) ==>
  bounded_object_positive_q_interval64_decimal
    (Pair
      (Pair (Pair (Num left_lower) (Num 0))
        (Num (left_lower_denominator - 1)))
      (Pair (Pair (Num left_upper) (Num 0))
        (Num (left_upper_denominator - 1)))) =
  bounded_object_positive_q_interval64_decimal
    (Pair
      (Pair (Pair (Num right_lower) (Num 0))
        (Num (right_lower_denominator - 1)))
      (Pair (Pair (Num right_upper) (Num 0))
        (Num (right_upper_denominator - 1))))
Proof
  strip_tac
  >> `bounded_object_positive_q_floor64_decimal
        (Pair (Pair (Num left_lower) (Num 0))
          (Num (left_lower_denominator - 1))) =
      bounded_object_positive_q_floor64_decimal
        (Pair (Pair (Num right_lower) (Num 0))
          (Num (right_lower_denominator - 1)))` by
       (irule registered_case10173_positive_q_floor64_decimal_equiv
        >> asm_rewrite_tac [])
  >> `bounded_object_positive_q_ceil64_decimal
        (Pair (Pair (Num left_upper) (Num 0))
          (Num (left_upper_denominator - 1))) =
      bounded_object_positive_q_ceil64_decimal
        (Pair (Pair (Num right_upper) (Num 0))
          (Num (right_upper_denominator - 1)))` by
       (irule registered_case10173_positive_q_ceil64_decimal_equiv
        >> asm_rewrite_tac [])
  >> simp
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def]
QED

val _ = export_theory ();
