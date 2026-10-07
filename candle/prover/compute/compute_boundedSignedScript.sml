(*
  Canonical signed endpoints for the fixed-scale nonlinear executor.

  The hot arithmetic remains the proved unsigned radix-22 word product from
  compute_bounded.  This layer adds only the exact remainder test, the
  one-unit ceiling correction, and sign-directed floor/ceiling selection.
  The option result remains an explicit overflow boundary even though the
  word64-by-word64, shift-40 specialization is proved to fit in bounded128.
*)
Theory compute_boundedSigned
Ancestors
  compute_bounded arithmetic words
Libs
  bossLib intLib

val _ = numLib.temp_prefer_num ();

Datatype:
  bounded_signed64 = BoundedSigned64 bool word64
End

Datatype:
  bounded_signed128 = BoundedSigned128 bool bounded128
End

Definition bounded128_is_zero_def:
  bounded128_is_zero (Bounded128 high low) =
    (high = 0w ∧ low = 0w)
End

Definition bounded_signed128_make_def:
  bounded_signed128_make negative magnitude =
    BoundedSigned128
      (negative ∧ ¬bounded128_is_zero magnitude) magnitude
End

Definition bounded_signed128_normalized_def:
  bounded_signed128_normalized (BoundedSigned128 negative magnitude) ⇔
    ¬negative ∨ ¬bounded128_is_zero magnitude
End

Definition bounded_signed128_negative_def:
  bounded_signed128_negative (BoundedSigned128 negative magnitude) = negative
End

Definition bounded_signed128_magnitude_def:
  bounded_signed128_magnitude (BoundedSigned128 negative magnitude) = magnitude
End

Theorem bounded128_is_zero_iff:
  bounded128_is_zero value ⇔ bounded128_to_num value = 0
Proof
  Cases_on `value`
  >> simp [bounded128_is_zero_def, bounded128_to_num_def,
           bounded_word_base_positive, wordsTheory.w2n_eq_0]
  >> metis_tac []
QED

Theorem bounded_signed128_make_normalized:
  bounded_signed128_normalized
    (bounded_signed128_make negative magnitude)
Proof
  Cases_on `magnitude`
  >> simp [bounded_signed128_make_def, bounded_signed128_normalized_def,
           bounded128_is_zero_def]
QED

Theorem bounded_signed128_make_magnitude:
  bounded_signed128_magnitude
    (bounded_signed128_make negative magnitude) = magnitude
Proof
  simp [bounded_signed128_make_def, bounded_signed128_magnitude_def]
QED

Theorem bounded_signed128_make_negative:
  bounded_signed128_negative
    (bounded_signed128_make negative magnitude) =
    (negative ∧ bounded128_to_num magnitude ≠ 0)
Proof
  simp [bounded_signed128_make_def, bounded_signed128_negative_def,
        bounded128_is_zero_iff]
QED

(* Natural-number ceiling division, stated in the form used by the checked
   word operation below. *)
Theorem bounded_div_ceil:
  0 < divisor ⇒
  (value + (divisor - 1)) DIV divisor =
    value DIV divisor + if value MOD divisor = 0 then 0 else 1
Proof
  strip_tac
  >> qabbrev_tac `quotient = value DIV divisor`
  >> qabbrev_tac `remainder = value MOD divisor`
  >> `remainder < divisor` by (qunabbrev_tac `remainder` >> simp [])
  >> `value = quotient * divisor + remainder` by
       (qunabbrev_tac `quotient`
        >> qunabbrev_tac `remainder`
        >> metis_tac [DIVISION])
  >> Cases_on `remainder = 0`
  >- (asm_simp_tac std_ss []
      >> `value + (divisor - 1) =
          quotient * divisor + (divisor - 1)` by intLib.ARITH_TAC
      >> pop_assum (fn th => once_rewrite_tac [th])
      >> irule DIV_UNIQUE
      >> qexists_tac `divisor - 1`
      >> simp [])
  >> asm_simp_tac std_ss []
  >> `0 < remainder` by simp []
  >> `value + (divisor - 1) =
      (quotient + 1) * divisor + (remainder - 1)` by intLib.ARITH_TAC
  >> pop_assum (fn th => once_rewrite_tac [th])
  >> irule DIV_UNIQUE
  >> qexists_tac `remainder - 1`
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_div_ceil40:
  (value + 1099511627775) DIV 1099511627776 =
    value DIV 1099511627776 +
      if value MOD 1099511627776 = 0 then 0 else 1
Proof
  mp_tac
    (Q.INST [`divisor` |-> `1099511627776`] bounded_div_ceil)
  >> simp []
QED

Definition bounded_word64_low40_nonzero_def:
  bounded_word64_low40_nonzero (word:word64) =
    (word_and word 1099511627775w ≠ 0w)
End

Theorem bounded_word64_mask40:
  (word:word64) && 1099511627775w =
    n2w (w2n word MOD 1099511627776)
Proof
  once_rewrite_tac [WORD_AND_COMM]
  >> mp_tac
       (Q.SPECL [`40`, `w2n (word:word64)`]
          (WORD_AND_EXP_SUB1 |> INST_TYPE [alpha |-> ``:64``]))
  >> simp [n2w_w2n]
QED

Theorem bounded_word64_low40_nonzero_correct:
  bounded_word64_low40_nonzero word ⇔
    w2n word MOD 1099511627776 ≠ 0
Proof
  rw [bounded_word64_low40_nonzero_def, bounded_word64_mask40]
  >> `w2n word MOD 1099511627776 < 1099511627776` by
       (irule MOD_LESS >> EVAL_TAC)
  >> `w2n word MOD 1099511627776 < 18446744073709551616` by
       intLib.ARITH_TAC
  >> simp [LESS_MOD]
QED

Theorem bounded_word64_product_low40:
  let product = bounded_word64_mul_full_chunks22 left right in
  (w2n left * w2n right) MOD 1099511627776 =
    w2n (SND product) MOD 1099511627776
Proof
  rw [LET_THM]
  >> mp_tac bounded_word64_mul_full_chunks22_correct
  >> simp [LET_THM, bounded_word_base_eq]
  >> strip_tac
  >> qpat_x_assum `_ = w2n left * w2n right`
       (fn th => once_rewrite_tac [GSYM th])
  >> simp [ADD_MOD, MOD_TIMES]
QED

Theorem bounded_word64_product_low40_nonzero:
  bounded_word64_low40_nonzero
    (SND (bounded_word64_mul_full_chunks22 left right)) ⇔
  (w2n left * w2n right) MOD 1099511627776 ≠ 0
Proof
  rw [bounded_word64_low40_nonzero_correct]
  >> mp_tac bounded_word64_product_low40
  >> simp [LET_THM]
QED

Definition bounded_word64_mul_shift_ceil40_def:
  bounded_word64_mul_shift_ceil40 (left:word64) (right:word64) =
    let product = bounded_word64_mul_full_chunks22 left right in
    let floor_result = bounded_word64_mul_shift_floor40 left right in
    if bounded_word64_low40_nonzero (SND product) then
      bounded128_add_words floor_result (Bounded128 0w 1w)
    else SOME floor_result
End

Theorem bounded_word64_mul_shift_floor40_plus_one_fits:
  bounded128_to_num (bounded_word64_mul_shift_floor40 left right) + 1 <
    bounded128_limit
Proof
  rw [bounded_word64_mul_shift_floor40_correct]
  >> qspec_then `left` assume_tac w2n_lt
  >> qspec_then `right` assume_tac w2n_lt
  >> `w2n left * w2n right <
      18446744073709551616 * 18446744073709551616` by
       (irule bounded_product_lt_square >> fs [dimword_64])
  >> `w2n left * w2n right DIV 1099511627776 <
      309485009821345068724781056` by
       (simp [DIV_LT_X] >> intLib.ARITH_TAC)
  >> rw [bounded128_limit_eq]
  >> intLib.ARITH_TAC
QED

Theorem bounded_word64_mul_shift_floor40_add_one:
  ∃result.
    bounded128_add_words
      (bounded_word64_mul_shift_floor40 left right)
      (Bounded128 0w 1w) = SOME result ∧
    bounded128_to_num result =
      (w2n left * w2n right) DIV 1099511627776 + 1
Proof
  rw [bounded128_add_words_refines, bounded128_add_def]
  >> simp [bounded128_to_num_def,
           bounded_word64_mul_shift_floor40_correct]
  >> Cases_on
       `bounded128_of_num
          (w2n left * w2n right DIV 1099511627776 + 1)`
  >- (fs [bounded128_of_num_none]
      >> mp_tac bounded_word64_mul_shift_floor40_plus_one_fits
      >> simp [bounded_word64_mul_shift_floor40_correct])
  >> qexists_tac `x`
  >> simp []
  >> metis_tac [bounded128_of_num_some]
QED

Theorem bounded_word64_mul_shift_ceil40_correct:
  ∃result.
    bounded_word64_mul_shift_ceil40 left right = SOME result ∧
    bounded128_to_num result =
      ((w2n left * w2n right) + 1099511627775) DIV 1099511627776
Proof
  Cases_on
    `(w2n left * w2n right) MOD 1099511627776 = 0`
  >- (rw [bounded_word64_mul_shift_ceil40_def, LET_THM,
          bounded_word64_product_low40_nonzero]
      >> simp [bounded_word64_mul_shift_floor40_correct,
               bounded_div_ceil40])
  >> rw [bounded_word64_mul_shift_ceil40_def, LET_THM,
         bounded_word64_product_low40_nonzero]
  >> mp_tac bounded_word64_mul_shift_floor40_add_one
  >> strip_tac
  >> qexists_tac `result`
  >> asm_rewrite_tac []
  >> simp [bounded_div_ceil40]
QED

Definition bounded_signed_word64_mul_floor40_def:
  bounded_signed_word64_mul_floor40
      (BoundedSigned64 left_negative left)
      (BoundedSigned64 right_negative right) =
    let negative = ¬(left_negative = right_negative) in
    if negative then
      case bounded_word64_mul_shift_ceil40 left right of
      | NONE => NONE
      | SOME magnitude => SOME (bounded_signed128_make T magnitude)
    else
      SOME
        (bounded_signed128_make F
          (bounded_word64_mul_shift_floor40 left right))
End

Definition bounded_signed_word64_mul_ceil40_def:
  bounded_signed_word64_mul_ceil40
      (BoundedSigned64 left_negative left)
      (BoundedSigned64 right_negative right) =
    let negative = ¬(left_negative = right_negative) in
    if negative then
      SOME
        (bounded_signed128_make T
          (bounded_word64_mul_shift_floor40 left right))
    else
      case bounded_word64_mul_shift_ceil40 left right of
      | NONE => NONE
      | SOME magnitude => SOME (bounded_signed128_make F magnitude)
End

Theorem bounded_signed_word64_mul_floor40_total:
  ∃result.
    bounded_signed_word64_mul_floor40 left right = SOME result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed_word64_mul_floor40_def]
  >> mp_tac
       (Q.INST [`left` |-> `(c:word64)`, `right` |-> `(c':word64)`]
          bounded_word64_mul_shift_ceil40_correct)
  >> strip_tac
  >> asm_rewrite_tac []
  >> qexists_tac `bounded_signed128_make T result`
  >> simp []
QED

Theorem bounded_signed_word64_mul_ceil40_total:
  ∃result.
    bounded_signed_word64_mul_ceil40 left right = SOME result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed_word64_mul_ceil40_def]
  >> mp_tac
       (Q.INST [`left` |-> `(c:word64)`, `right` |-> `(c':word64)`]
          bounded_word64_mul_shift_ceil40_correct)
  >> strip_tac
  >> asm_rewrite_tac []
  >> qexists_tac `bounded_signed128_make F result`
  >> simp []
QED

Theorem bounded_signed_word64_mul_floor40_normalized:
  bounded_signed_word64_mul_floor40 left right = SOME result ⇒
  bounded_signed128_normalized result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed_word64_mul_floor40_def]
  >> Cases_on `bounded_word64_mul_shift_ceil40 c c'`
  >> gvs [bounded_signed128_make_def, bounded_signed128_normalized_def]
QED

Theorem bounded_signed_word64_mul_ceil40_normalized:
  bounded_signed_word64_mul_ceil40 left right = SOME result ⇒
  bounded_signed128_normalized result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed_word64_mul_ceil40_def]
  >> Cases_on `bounded_word64_mul_shift_ceil40 c c'`
  >> gvs [bounded_signed128_make_def, bounded_signed128_normalized_def]
QED

Theorem bounded_signed_word64_mul_floor40_magnitude:
  bounded_signed_word64_mul_floor40
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ⇒
  bounded128_to_num (bounded_signed128_magnitude result) =
    (if left_negative ≠ right_negative then
       (w2n left_word * w2n right_word + 1099511627775) DIV
         1099511627776
     else
       (w2n left_word * w2n right_word) DIV 1099511627776)
Proof
  Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [bounded_signed_word64_mul_floor40_def,
         bounded_signed128_make_magnitude,
         bounded_word64_mul_shift_floor40_correct]
  >> Cases_on `bounded_word64_mul_shift_ceil40 left_word right_word`
  >> fs [bounded_signed128_make_magnitude]
  >> mp_tac
       (Q.INST
          [`left` |-> `(left_word:word64)`,
           `right` |-> `(right_word:word64)`]
          bounded_word64_mul_shift_ceil40_correct)
  >> simp []
  >> metis_tac
       [bounded_signed128_make_magnitude,
        bounded_word64_mul_shift_floor40_correct]
QED

Theorem bounded_signed_word64_mul_ceil40_magnitude:
  bounded_signed_word64_mul_ceil40
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ⇒
  bounded128_to_num (bounded_signed128_magnitude result) =
    (if left_negative ≠ right_negative then
       (w2n left_word * w2n right_word) DIV 1099511627776
     else
       (w2n left_word * w2n right_word + 1099511627775) DIV
         1099511627776)
Proof
  Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [bounded_signed_word64_mul_ceil40_def,
         bounded_signed128_make_magnitude,
         bounded_word64_mul_shift_floor40_correct]
  >> Cases_on `bounded_word64_mul_shift_ceil40 left_word right_word`
  >> fs [bounded_signed128_make_magnitude]
  >> mp_tac
       (Q.INST
          [`left` |-> `(left_word:word64)`,
           `right` |-> `(right_word:word64)`]
          bounded_word64_mul_shift_ceil40_correct)
  >> simp []
  >> metis_tac
       [bounded_signed128_make_magnitude,
        bounded_word64_mul_shift_floor40_correct]
QED

Theorem bounded_signed_word64_mul_floor40_negative:
  bounded_signed_word64_mul_floor40
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ⇒
  bounded_signed128_negative result =
    (left_negative ≠ right_negative ∧
     (w2n left_word * w2n right_word + 1099511627775) DIV
       1099511627776 ≠ 0)
Proof
  Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [bounded_signed_word64_mul_floor40_def,
         bounded_signed128_make_negative]
  >> Cases_on `bounded_word64_mul_shift_ceil40 left_word right_word`
  >> fs [bounded_signed128_make_negative]
  >> mp_tac
       (Q.INST
          [`left` |-> `(left_word:word64)`,
           `right` |-> `(right_word:word64)`]
          bounded_word64_mul_shift_ceil40_correct)
  >> simp []
  >> metis_tac [bounded_signed128_make_negative]
QED

Theorem bounded_signed_word64_mul_ceil40_negative:
  bounded_signed_word64_mul_ceil40
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME result ⇒
  bounded_signed128_negative result =
    (left_negative ≠ right_negative ∧
     (w2n left_word * w2n right_word) DIV 1099511627776 ≠ 0)
Proof
  Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> Cases_on `result`
  >> gvs [bounded_signed_word64_mul_ceil40_def,
          bounded_signed128_make_negative,
          bounded_signed128_make_def,
          bounded_signed128_negative_def,
          bounded128_is_zero_iff,
          bounded_word64_mul_shift_floor40_correct]
  >> Cases_on `bounded_word64_mul_shift_ceil40 left_word right_word`
  >> gvs [bounded_signed128_make_negative,
          bounded_signed128_make_def,
          bounded_signed128_negative_def,
          bounded128_is_zero_iff]
QED

Theorem bounded_signed_word64_mul_directed_contract:
  let product = w2n left_word * w2n right_word in
  let floor_magnitude = product DIV 1099511627776 in
  let ceil_magnitude =
    (product + 1099511627775) DIV 1099511627776 in
  bounded_signed_word64_mul_floor40
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME floor_result ∧
  bounded_signed_word64_mul_ceil40
      (BoundedSigned64 left_negative left_word)
      (BoundedSigned64 right_negative right_word) = SOME ceil_result ⇒
  bounded_signed128_normalized floor_result ∧
  bounded_signed128_normalized ceil_result ∧
  bounded_signed128_negative floor_result =
    (left_negative ≠ right_negative ∧ ceil_magnitude ≠ 0) ∧
  bounded_signed128_negative ceil_result =
    (left_negative ≠ right_negative ∧ floor_magnitude ≠ 0) ∧
  bounded128_to_num (bounded_signed128_magnitude floor_result) =
    (if left_negative ≠ right_negative then ceil_magnitude
     else floor_magnitude) ∧
  bounded128_to_num (bounded_signed128_magnitude ceil_result) =
    (if left_negative ≠ right_negative then floor_magnitude
     else ceil_magnitude)
Proof
  simp_tac std_ss [LET_THM]
  >> strip_tac
  >> imp_res_tac bounded_signed_word64_mul_floor40_normalized
  >> imp_res_tac bounded_signed_word64_mul_ceil40_normalized
  >> imp_res_tac bounded_signed_word64_mul_floor40_negative
  >> imp_res_tac bounded_signed_word64_mul_ceil40_negative
  >> imp_res_tac bounded_signed_word64_mul_floor40_magnitude
  >> imp_res_tac bounded_signed_word64_mul_ceil40_magnitude
  >> asm_rewrite_tac []
QED

Theorem bounded_signed_word64_mul_zero_canonical_test:
  bounded_signed_word64_mul_floor40
    (BoundedSigned64 T 0w) (BoundedSigned64 F 17w) =
      SOME (BoundedSigned128 F (Bounded128 0w 0w)) ∧
  bounded_signed_word64_mul_ceil40
    (BoundedSigned64 T 0w) (BoundedSigned64 F 17w) =
      SOME (BoundedSigned128 F (Bounded128 0w 0w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_signed_word64_mul_mixed_sign_test:
  bounded_signed_word64_mul_floor40
    (BoundedSigned64 T 1099511627777w)
    (BoundedSigned64 F 1099511627777w) =
      SOME
        (BoundedSigned128 T
          (Bounded128 0w 1099511627779w)) ∧
  bounded_signed_word64_mul_ceil40
    (BoundedSigned64 T 1099511627777w)
    (BoundedSigned64 F 1099511627777w) =
      SOME
        (BoundedSigned128 T
          (Bounded128 0w 1099511627778w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
