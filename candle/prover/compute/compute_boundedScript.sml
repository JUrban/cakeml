(*
  Fixed-width data boundary for a future checked Candle compute executor.

  This theory is deliberately independent of the compute-expression syntax.
  It establishes the lossless conversion boundary first; arithmetic and the
  executor refinement will be layered on it.  Overflow remains an explicit
  option at every conversion from an unbounded natural.
*)
Theory compute_bounded
Ancestors
  arithmetic words
Libs
  bossLib intLib

val _ = numLib.temp_prefer_num ();

Definition bounded_word_base_def:
  bounded_word_base = dimword (:64)
End

Definition bounded128_limit_def:
  bounded128_limit = bounded_word_base * bounded_word_base
End

Definition bounded192_limit_def:
  bounded192_limit =
    bounded_word_base * bounded_word_base * bounded_word_base
End

Theorem bounded_word_base_positive:
  0 < bounded_word_base
Proof
  simp [bounded_word_base_def]
QED

Theorem bounded_word_base_eq:
  bounded_word_base = 18446744073709551616
Proof
  simp [bounded_word_base_def]
QED

Theorem bounded128_limit_eq:
  bounded128_limit = 2 ** 128
Proof
  simp [bounded128_limit_def, bounded_word_base_def, dimword_64,
        GSYM EXP_ADD]
QED

Theorem bounded192_limit_eq:
  bounded192_limit = 2 ** 192
Proof
  simp [bounded192_limit_def, bounded_word_base_def, dimword_64,
        GSYM EXP_ADD]
QED

Datatype:
  bounded128 = Bounded128 word64 word64
End

Datatype:
  bounded192 = Bounded192 word64 word64 word64
End

Definition bounded128_to_num_def:
  bounded128_to_num (Bounded128 high low) =
    w2n low + bounded_word_base * w2n high
End

Definition bounded192_to_num_def:
  bounded192_to_num (Bounded192 high middle low) =
    w2n low + bounded_word_base * w2n middle +
    bounded_word_base * bounded_word_base * w2n high
End

Definition bounded128_of_num_def:
  bounded128_of_num n =
    if n < bounded128_limit then
      SOME (Bounded128 (n2w (n DIV bounded_word_base)) (n2w n))
    else NONE
End

Definition bounded192_of_num_def:
  bounded192_of_num n =
    if n < bounded192_limit then
      SOME
        (Bounded192
          (n2w (n DIV (bounded_word_base * bounded_word_base)))
          (n2w (n DIV bounded_word_base))
          (n2w n))
    else NONE
End

Theorem bounded128_to_num_lt:
  bounded128_to_num (Bounded128 high low) < bounded128_limit
Proof
  rw [bounded128_to_num_def]
  >> qspec_then ‘low’ assume_tac w2n_lt
  >> qspec_then ‘high’ assume_tac w2n_lt
  >> gvs [bounded128_limit_def, bounded_word_base_def, dimword_64]
  >> intLib.ARITH_TAC
QED

Theorem bounded192_to_num_lt:
  bounded192_to_num (Bounded192 high middle low) < bounded192_limit
Proof
  rw [bounded192_to_num_def]
  >> qspec_then ‘low’ assume_tac w2n_lt
  >> qspec_then ‘middle’ assume_tac w2n_lt
  >> qspec_then ‘high’ assume_tac w2n_lt
  >> gvs [bounded192_limit_def, bounded_word_base_def, dimword_64]
  >> intLib.ARITH_TAC
QED

Theorem bounded128_of_num_none:
  bounded128_of_num n = NONE ⇔ bounded128_limit ≤ n
Proof
  simp [bounded128_of_num_def, NOT_LESS]
QED

Theorem bounded192_of_num_none:
  bounded192_of_num n = NONE ⇔ bounded192_limit ≤ n
Proof
  simp [bounded192_of_num_def, NOT_LESS]
QED

Theorem bounded_two_digit_reconstruct:
  0 < base ∧ n < base * base ⇒
  n MOD base + base * ((n DIV base) MOD base) = n
Proof
  strip_tac
  >> ‘n DIV base < base’ by simp [DIV_LT_X]
  >> ‘(n DIV base) MOD base = n DIV base’ by simp []
  >> ‘n = (n DIV base) * base + n MOD base’ by
       metis_tac [DIVISION]
  >> metis_tac [ADD_COMM, MULT_COMM]
QED

Theorem bounded_three_digit_group:
  remainder + base * middle + base * base * high =
  remainder + base * (middle + base * high)
Proof
  once_rewrite_tac [LEFT_ADD_DISTRIB]
  >> once_rewrite_tac [GSYM MULT_ASSOC]
  >> once_rewrite_tac [GSYM ADD_ASSOC]
  >> simp []
QED

Theorem bounded_three_digit_reorder:
  middle + (high + low) = low + middle + high
Proof
  metis_tac [ADD_ASSOC, ADD_COMM]
QED

Theorem bounded_division_reconstruct:
  0 < base ⇒ n MOD base + base * (n DIV base) = n
Proof
  strip_tac
  >> ‘n = (n DIV base) * base + n MOD base’ by
       metis_tac [DIVISION]
  >> metis_tac [ADD_COMM, MULT_COMM]
QED

Theorem bounded_three_digit_reconstruct:
  0 < base ∧ n < base * base * base ⇒
  n MOD base + base * ((n DIV base) MOD base) +
    base * base * ((n DIV (base * base)) MOD base) = n
Proof
  strip_tac
  >> ‘n DIV base < base * base’ by simp [DIV_LT_X, MULT_ASSOC]
  >> ‘(n DIV base) MOD base +
       base * ((n DIV (base * base)) MOD base) = n DIV base’ by
       (simp [GSYM DIV_DIV_DIV_MULT]
        >> once_rewrite_tac [ADD_COMM]
        >> irule bounded_two_digit_reconstruct
        >> simp [])
  >> once_rewrite_tac [bounded_three_digit_group]
  >> qpat_x_assum
       ‘(n DIV base) MOD base +
        base * ((n DIV (base * base)) MOD base) = n DIV base’
       (fn th => once_rewrite_tac [th])
  >> irule bounded_division_reconstruct
  >> simp []
QED

Theorem bounded128_of_num_some:
  bounded128_of_num n = SOME value ⇒
  bounded128_to_num value = n
Proof
  rw [bounded128_of_num_def]
  >> gvs [bounded128_to_num_def]
  >> simp [bounded_word_base_def, w2n_n2w]
  >> irule bounded_two_digit_reconstruct
  >> fs [bounded128_limit_def, bounded_word_base_def]
QED

Theorem bounded192_of_num_some:
  bounded192_of_num n = SOME value ⇒
  bounded192_to_num value = n
Proof
  rw [bounded192_of_num_def]
  >> gvs [bounded192_to_num_def]
  >> simp [w2n_n2w, GSYM bounded_word_base_def]
  >> rewrite_tac [GSYM bounded_word_base_eq]
  >> once_rewrite_tac [bounded_three_digit_reorder]
  >> rewrite_tac [EXP_2]
  >> irule bounded_three_digit_reconstruct
  >> fs [bounded192_limit_def]
  >> simp [bounded_word_base_positive]
QED

(*
  Logical contracts for the first checked arithmetic operations.  These use
  the conversion boundary above and deliberately do not claim fast execution;
  a word-level implementation must refine these total option-valued functions.
*)

Definition bounded128_add_def:
  bounded128_add left right =
    bounded128_of_num
      (bounded128_to_num left + bounded128_to_num right)
End

Definition bounded192_add_def:
  bounded192_add left right =
    bounded192_of_num
      (bounded192_to_num left + bounded192_to_num right)
End

Definition bounded128_mul_to_192_def:
  bounded128_mul_to_192 left right =
    bounded192_of_num
      (bounded128_to_num left * bounded128_to_num right)
End

Definition bounded192_narrow_128_def:
  bounded192_narrow_128 value =
    bounded128_of_num (bounded192_to_num value)
End

Definition bounded192_shift_floor_128_def:
  bounded192_shift_floor_128 bits value =
    bounded128_of_num
      (bounded192_to_num value DIV (2 ** bits))
End

Definition bounded192_shift_ceil_128_def:
  bounded192_shift_ceil_128 bits value =
    bounded128_of_num
      ((bounded192_to_num value + (2 ** bits - 1)) DIV (2 ** bits))
End

Theorem bounded128_add_none:
  bounded128_add left right = NONE ⇔
  bounded128_limit ≤
    bounded128_to_num left + bounded128_to_num right
Proof
  simp [bounded128_add_def, bounded128_of_num_none]
QED

Theorem bounded192_add_none:
  bounded192_add left right = NONE ⇔
  bounded192_limit ≤
    bounded192_to_num left + bounded192_to_num right
Proof
  simp [bounded192_add_def, bounded192_of_num_none]
QED

Theorem bounded128_mul_to_192_none:
  bounded128_mul_to_192 left right = NONE ⇔
  bounded192_limit ≤
    bounded128_to_num left * bounded128_to_num right
Proof
  simp [bounded128_mul_to_192_def, bounded192_of_num_none]
QED

Theorem bounded192_narrow_128_none:
  bounded192_narrow_128 value = NONE ⇔
  bounded128_limit ≤ bounded192_to_num value
Proof
  simp [bounded192_narrow_128_def, bounded128_of_num_none]
QED

Theorem bounded192_shift_floor_128_none:
  bounded192_shift_floor_128 bits value = NONE ⇔
  bounded128_limit ≤
    bounded192_to_num value DIV (2 ** bits)
Proof
  simp [bounded192_shift_floor_128_def, bounded128_of_num_none]
QED

Theorem bounded192_shift_ceil_128_none:
  bounded192_shift_ceil_128 bits value = NONE ⇔
  bounded128_limit ≤
    (bounded192_to_num value + (2 ** bits - 1)) DIV (2 ** bits)
Proof
  simp [bounded192_shift_ceil_128_def, bounded128_of_num_none]
QED

Theorem bounded128_add_some:
  bounded128_add left right = SOME result ⇒
  bounded128_to_num result =
    bounded128_to_num left + bounded128_to_num right
Proof
  rw [bounded128_add_def]
  >> imp_res_tac bounded128_of_num_some
QED

Theorem bounded192_add_some:
  bounded192_add left right = SOME result ⇒
  bounded192_to_num result =
    bounded192_to_num left + bounded192_to_num right
Proof
  rw [bounded192_add_def]
  >> imp_res_tac bounded192_of_num_some
QED

Theorem bounded128_mul_to_192_some:
  bounded128_mul_to_192 left right = SOME result ⇒
  bounded192_to_num result =
    bounded128_to_num left * bounded128_to_num right
Proof
  rw [bounded128_mul_to_192_def]
  >> imp_res_tac bounded192_of_num_some
QED

Theorem bounded192_narrow_128_some:
  bounded192_narrow_128 value = SOME result ⇒
  bounded128_to_num result = bounded192_to_num value
Proof
  rw [bounded192_narrow_128_def]
  >> imp_res_tac bounded128_of_num_some
QED

Theorem bounded192_shift_floor_128_some:
  bounded192_shift_floor_128 bits value = SOME result ⇒
  bounded128_to_num result =
    bounded192_to_num value DIV (2 ** bits)
Proof
  rw [bounded192_shift_floor_128_def]
  >> imp_res_tac bounded128_of_num_some
QED

Theorem bounded192_shift_ceil_128_some:
  bounded192_shift_ceil_128 bits value = SOME result ⇒
  bounded128_to_num result =
    (bounded192_to_num value + (2 ** bits - 1)) DIV (2 ** bits)
Proof
  rw [bounded192_shift_ceil_128_def]
  >> imp_res_tac bounded128_of_num_some
QED

(* First executable word operation.  The signed interval layer will use this
   unsigned magnitude primitive and keep sign handling outside the carry
   chain. *)

Definition bounded_word64_add_carry_def:
  bounded_word64_add_carry (left:word64) (right:word64) carry_in =
    let partial = left + right in
    let partial_carry = word_lo partial left in
    if carry_in then
      let result = partial + 1w in
      (result, partial_carry ∨ result = 0w)
    else
      (partial, partial_carry)
End

Theorem bounded_add_mod_carry:
  0 < base ∧ left < base ∧ right < base ⇒
  ((left + right) MOD base < left ⇔ base ≤ left + right)
Proof
  strip_tac
  >> Cases_on ‘left + right < base’
  >- (simp [LESS_MOD] >> intLib.ARITH_TAC)
  >> ‘(left + right) MOD base = left + right - base’ by
       (irule MOD_UNIQUE
        >> qexists_tac ‘1’
        >> simp []
        >> intLib.ARITH_TAC)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_add_mod_carry_in:
  0 < base ∧ left < base ∧ right < base ⇒
  ((left + right) MOD base < left ∨
   (left + (right + 1)) MOD base = 0 ⇔
   base ≤ left + (right + 1))
Proof
  strip_tac
  >> ‘((left + right) MOD base < left ⇔ base ≤ left + right)’ by
       metis_tac [bounded_add_mod_carry]
  >> rw []
  >> Cases_on ‘base ≤ left + right’
  >- simp []
  >> Cases_on ‘base ≤ left + (right + 1)’
  >- (‘left + (right + 1) = base’ by intLib.ARITH_TAC
      >> simp [])
  >> ‘left + (right + 1) < base’ by intLib.ARITH_TAC
  >> simp [LESS_MOD]
QED

Theorem bounded_word64_add_carry_correct:
  bounded_word64_add_carry left right carry_in =
    (FST (add_with_carry (left, right, carry_in)),
     FST (SND (add_with_carry (left, right, carry_in))))
Proof
  Cases_on ‘carry_in’
  >> Cases_on ‘left’
  >> Cases_on ‘right’
  >> simp [bounded_word64_add_carry_def, add_with_carry_def,
           word_add_n2w, WORD_LO, dimword_64, NOT_LESS]
  >- (irule bounded_add_mod_carry_in
      >> simp [dimword_64])
  >> irule bounded_add_mod_carry
  >> simp [dimword_64]
QED

Definition bounded128_add_words_def:
  bounded128_add_words
      (Bounded128 left_high left_low)
      (Bounded128 right_high right_low) =
    let low_sum = bounded_word64_add_carry left_low right_low F in
    let high_sum = bounded_word64_add_carry
      left_high right_high (SND low_sum) in
    if SND high_sum then NONE
    else SOME (Bounded128 (FST high_sum) (FST low_sum))
End

Theorem bounded128_add_words_refines:
  bounded128_add_words left right = bounded128_add left right
Proof
  Cases_on ‘left’
  >> Cases_on ‘right’
  >> qspec_then ‘c’ assume_tac w2n_lt
  >> qspec_then ‘c0’ assume_tac w2n_lt
  >> qspec_then ‘c'’ assume_tac w2n_lt
  >> qspec_then ‘c0'’ assume_tac w2n_lt
  >> rw [bounded128_add_words_def, bounded128_add_def,
         bounded128_of_num_def, bounded128_to_num_def,
         bounded_word64_add_carry_correct, add_with_carry_def]
  >> fs [bounded_word_base_def, bounded128_limit_def, dimword_64]
  >> intLib.ARITH_TAC
QED

Definition bounded128_add_repeat_def:
  bounded128_add_repeat 0 increment value = SOME value ∧
  bounded128_add_repeat (SUC count) increment value =
    case bounded128_add value increment of
    | NONE => NONE
    | SOME next => bounded128_add_repeat count increment next
End

Definition bounded128_add_words_repeat_def:
  bounded128_add_words_repeat 0 increment value = SOME value ∧
  bounded128_add_words_repeat (SUC count) increment value =
    case bounded128_add_words value increment of
    | NONE => NONE
    | SOME next => bounded128_add_words_repeat count increment next
End

Theorem bounded128_add_words_repeat_refines:
  ∀n increment value.
    bounded128_add_words_repeat n increment value =
      bounded128_add_repeat n increment value
Proof
  Induct
  >> simp [bounded128_add_words_repeat_def, bounded128_add_repeat_def,
           bounded128_add_words_refines]
  >> Cases_on ‘bounded128_add value increment’
  >> simp []
QED

Definition bounded128_repeat_control_def:
  bounded128_repeat_control 0 value = SOME value ∧
  bounded128_repeat_control (SUC n) (Bounded128 high low) =
    let low_copy = (low, F) in
    let high_copy = (high, SND low_copy) in
    if SND high_copy then NONE
    else bounded128_repeat_control n
      (Bounded128 (FST high_copy) (FST low_copy))
End

Definition bounded128_add_words_benchmark_def:
  bounded128_add_words_benchmark =
    bounded128_add_words_repeat 10000000
      (Bounded128 0w 1w) (Bounded128 0w 0w)
End

Definition bounded128_repeat_control_benchmark_def:
  bounded128_repeat_control_benchmark =
    bounded128_repeat_control 10000000 (Bounded128 0w 0w)
End

Definition bounded128_add_words_benchmark_ok_def:
  bounded128_add_words_benchmark_ok ⇔
    bounded128_add_words_benchmark =
      SOME (Bounded128 0w 10000000w)
End

Definition bounded128_repeat_control_benchmark_ok_def:
  bounded128_repeat_control_benchmark_ok ⇔
    bounded128_repeat_control_benchmark =
      SOME (Bounded128 0w 0w)
End

Theorem bounded128_add_words_repeat_small_test:
  bounded128_add_words_repeat 3
    (Bounded128 0w 7w) (Bounded128 0w 5w) =
  SOME (Bounded128 0w 26w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded128_add_words_no_carry_test:
  bounded128_add_words
    (Bounded128 0w 7w) (Bounded128 0w 9w) =
  SOME (Bounded128 0w 16w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded128_add_words_low_carry_test:
  bounded128_add_words
    (Bounded128 0w (-1w)) (Bounded128 0w 1w) =
  SOME (Bounded128 1w 0w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded128_add_words_overflow_test:
  bounded128_add_words
    (Bounded128 (-1w) (-1w)) (Bounded128 0w 1w) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Definition bounded192_add_words_def:
  bounded192_add_words
      (Bounded192 left_high left_middle left_low)
      (Bounded192 right_high right_middle right_low) =
    let low_sum = bounded_word64_add_carry left_low right_low F in
    let middle_sum = bounded_word64_add_carry
      left_middle right_middle (SND low_sum) in
    let high_sum = bounded_word64_add_carry
      left_high right_high (SND middle_sum) in
    if SND high_sum then NONE
    else SOME
      (Bounded192 (FST high_sum) (FST middle_sum) (FST low_sum))
End

Theorem bounded192_add_words_refines:
  bounded192_add_words left right = bounded192_add left right
Proof
  Cases_on ‘left’
  >> Cases_on ‘right’
  >> qspec_then ‘c’ assume_tac w2n_lt
  >> qspec_then ‘c0’ assume_tac w2n_lt
  >> qspec_then ‘c1’ assume_tac w2n_lt
  >> qspec_then ‘c'’ assume_tac w2n_lt
  >> qspec_then ‘c0'’ assume_tac w2n_lt
  >> qspec_then ‘c1'’ assume_tac w2n_lt
  >> rw [bounded192_add_words_def, bounded192_add_def,
         bounded192_of_num_def, bounded192_to_num_def,
         bounded_word64_add_carry_correct, add_with_carry_def]
  >> fs [bounded_word_base_def, bounded192_limit_def, dimword_64]
  >> intLib.ARITH_TAC
QED

Theorem bounded192_add_words_carry_chain_test:
  bounded192_add_words
    (Bounded192 0w (-1w) (-1w)) (Bounded192 0w 0w 1w) =
  SOME (Bounded192 1w 0w 0w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded192_add_words_overflow_test:
  bounded192_add_words
    (Bounded192 (-1w) (-1w) (-1w)) (Bounded192 0w 0w 1w) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
