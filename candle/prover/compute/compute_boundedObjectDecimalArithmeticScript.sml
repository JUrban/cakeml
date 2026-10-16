(*****************************************************************************
 * Exact arithmetic bridge from the bounded decimal carrier to the signed
 * fixed-scale representation used by the authenticated object checker.
 *
 * These definitions are the ordinary-cv meanings of the corresponding
 * [candle_cv_fs_*] source equations.  The first refinement lemmas show that
 * a successful bounded directed product has exactly the same canonical cv
 * result as the object's raw signed product followed by decimal rounding.
 *****************************************************************************)
Theory compute_boundedObjectDecimalArithmetic
Ancestors
  compute_boundedIntervalDecimal compute_boundedObjectDecimalDecode
Libs
  bossLib preamble intLib

val _ = numLib.temp_prefer_num ();

Definition bounded_object_fs_raw_mul_def:
  bounded_object_fs_raw_mul
      (Pair (Num left_positive) (Num left_negative) : cv)
      (Pair (Num right_positive) (Num right_negative) : cv) =
    SOME
      (Pair
        (Num (left_positive * right_positive +
              left_negative * right_negative))
        (Num (left_positive * right_negative +
              left_negative * right_positive))) /\
  bounded_object_fs_raw_mul _ _ = NONE
End

Definition bounded_object_q_ceil_div_def:
  bounded_object_q_ceil_div numerator denominator =
    numerator DIV denominator +
      if numerator MOD denominator = 0 then 0 else 1
End

Definition bounded_object_fs_floor_div_def:
  bounded_object_fs_floor_div
      (Pair (Num positive) (Num negative) : cv) denominator =
    (if positive < negative then
      SOME
        (Pair (Num 0)
          (Num
            (bounded_object_q_ceil_div
              (negative - positive) denominator)))
    else
      SOME
        (Pair (Num ((positive - negative) DIV denominator)) (Num 0))) /\
  bounded_object_fs_floor_div _ denominator = NONE
End

Definition bounded_object_fs_ceil_div_def:
  bounded_object_fs_ceil_div
      (Pair (Num positive) (Num negative) : cv) denominator =
    (if positive < negative then
      SOME
        (Pair (Num 0)
          (Num ((negative - positive) DIV denominator)))
    else
      SOME
        (Pair
          (Num
            (bounded_object_q_ceil_div
              (positive - negative) denominator))
          (Num 0))) /\
  bounded_object_fs_ceil_div _ denominator = NONE
End

Theorem bounded_object_q_ceil_div_decimal:
  bounded_object_q_ceil_div numerator 1000000000000 =
    (numerator + 999999999999) DIV 1000000000000
Proof
  simp [bounded_object_q_ceil_div_def]
  >> rpt strip_tac
  >> mp_tac
       (Q.SPEC `1000000000000` arithmeticTheory.CEILING_DIV)
  >> simp [arithmeticTheory.CEILING_DIV_def, MIN_DEF]
QED

Theorem bounded_signed64_object_cv_nonnegative_value:
  bounded_signed64_normalized value /\
  bounded_signed64_to_int value = &magnitude ==>
  bounded_signed64_object_cv value =
    Pair (Num magnitude) (Num 0)
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative word`
  >> Cases_on `negative`
  >> simp [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
           compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_object_cv_negative_value:
  bounded_signed64_normalized value /\
  0 < magnitude /\
  bounded_signed64_to_int value = -(&magnitude) ==>
  bounded_signed64_object_cv value =
    Pair (Num 0) (Num magnitude)
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative word`
  >> Cases_on `negative`
  >> simp [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
           compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_object_cv_nonpositive_value:
  bounded_signed64_normalized value /\
  bounded_signed64_to_int value = -(&magnitude) ==>
  bounded_signed64_object_cv value =
    Pair (Num 0) (Num magnitude)
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative word`
  >> Cases_on `negative`
  >> simp [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
           compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_decimal_ceil_product_positive:
  (left_word : word64) <> 0w /\ right_word <> 0w ==>
  0 <
    (w2n left_word * w2n right_word + 999999999999) DIV
      1000000000000
Proof
  rpt strip_tac
  >> rw [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
         arithmeticTheory.DIV_EQ_0]
  >> qsuff_tac `0 < w2n left_word * w2n right_word`
  >- decide_tac
  >> simp [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
           MULT_EQ_0,
           wordsTheory.w2n_eq_0]
QED

Theorem bounded_scaled_mul_floor64_decimal_object_exact:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right /\
  bounded_scaled_mul_floor64_decimal left right = SOME result ==>
  ?raw.
    bounded_object_fs_raw_mul
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) = SOME raw /\
    bounded_object_fs_floor_div raw 1000000000000 =
      SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_scaled_mul_floor64_decimal
          (BoundedSigned64 left_negative left_word)
          (BoundedSigned64 right_negative right_word) = SOME result`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_value
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_normalized
  >> qexists_tac
       `Pair
          (Num
            ((if left_negative then 0 else w2n left_word) *
             (if right_negative then 0 else w2n right_word) +
             (if left_negative then w2n left_word else 0) *
             (if right_negative then w2n right_word else 0)))
          (Num
            ((if left_negative then 0 else w2n left_word) *
             (if right_negative then w2n right_word else 0) +
             (if left_negative then w2n left_word else 0) *
             (if right_negative then 0 else w2n right_word)))`
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> Cases_on `left_word = 0w`
  >> Cases_on `right_word = 0w`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
         compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
         bounded_object_fs_raw_mul_def,
         bounded_object_fs_floor_div_def,
         bounded_object_q_ceil_div_decimal,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
         wordsTheory.w2n_eq_0]
  >> TRY
       (irule bounded_signed64_object_cv_nonnegative_value
        >> simp [])
  >> TRY
       (sym_tac
        >> irule bounded_signed64_object_cv_nonnegative_value
        >> simp [])
  >> sym_tac
  >> irule bounded_signed64_object_cv_negative_value
  >> simp [bounded_decimal_ceil_product_positive]
QED

Theorem bounded_scaled_mul_ceil64_decimal_object_exact:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right /\
  bounded_scaled_mul_ceil64_decimal left right = SOME result ==>
  ?raw.
    bounded_object_fs_raw_mul
      (bounded_signed64_object_cv left)
      (bounded_signed64_object_cv right) = SOME raw /\
    bounded_object_fs_ceil_div raw 1000000000000 =
      SOME (bounded_signed64_object_cv result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_scaled_mul_ceil64_decimal
          (BoundedSigned64 left_negative left_word)
          (BoundedSigned64 right_negative right_word) = SOME result`
  >> strip_tac
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_value
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_normalized
  >> qexists_tac
       `Pair
          (Num
            ((if left_negative then 0 else w2n left_word) *
             (if right_negative then 0 else w2n right_word) +
             (if left_negative then w2n left_word else 0) *
             (if right_negative then w2n right_word else 0)))
          (Num
            ((if left_negative then 0 else w2n left_word) *
             (if right_negative then w2n right_word else 0) +
             (if left_negative then w2n left_word else 0) *
             (if right_negative then 0 else w2n right_word)))`
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> Cases_on `left_word = 0w`
  >> Cases_on `right_word = 0w`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
         compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
         bounded_object_fs_raw_mul_def,
         bounded_object_fs_ceil_div_def,
         bounded_object_q_ceil_div_decimal,
         GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
         wordsTheory.w2n_eq_0]
  >> TRY
       (irule bounded_signed64_object_cv_nonnegative_value
        >> simp [])
  >> TRY
       (sym_tac
        >> irule bounded_signed64_object_cv_nonnegative_value
        >> simp [])
  >> sym_tac
  >> irule bounded_signed64_object_cv_nonpositive_value
  >> simp []
QED

val _ = export_theory ();
