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
  >> once_rewrite_tac [ADD_COMM]
  >> irule bounded_two_digit_reconstruct
  >> fs [bounded128_limit_def, bounded_word_base_def]
QED

Theorem bounded192_of_num_some:
  bounded192_of_num n = SOME value ⇒
  bounded192_to_num value = n
Proof
  rw [bounded192_of_num_def]
  >> gvs [bounded192_to_num_def]
  >> simp [bounded_word_base_def, w2n_n2w]
  >> once_rewrite_tac [bounded_three_digit_reorder]
  >> rewrite_tac [EXP_2]
  >> irule bounded_three_digit_reconstruct
  >> fs [bounded192_limit_def, bounded_word_base_def]
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

val _ = export_theory ();
