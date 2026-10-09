(*****************************************************************************
 * Word-only 192-bit operations needed by Taylor completion.
 *
 * This DEVELOPMENT layer keeps the hot path out of arbitrary-precision
 * naturals.  It supplies the executable algorithms and closed carry/borrow
 * tests first.  Their general refinement to bounded192_to_num is an explicit
 * proof obligation before the complete checker can support a release claim.
 *****************************************************************************)
Theory compute_boundedWide
Ancestors
  compute_boundedSignedAdd compute_bounded
Libs
  bossLib preamble intLib

Definition bounded192_zero_def:
  bounded192_zero = Bounded192 0w 0w 0w
End

Definition bounded_word64_sub_borrow_in_def:
  bounded_word64_sub_borrow_in
      (left:word64) (right:word64) borrow_in =
    let first = bounded_word64_sub_borrow left right in
    if borrow_in then
      let second = bounded_word64_sub_borrow (FST first) 1w in
      (FST second, SND first ∨ SND second)
    else first
End

Definition bounded192_le_words_def:
  bounded192_le_words
      (Bounded192 left_high left_middle left_low)
      (Bounded192 right_high right_middle right_low) =
    (word_lo left_high right_high ∨
     (left_high = right_high ∧
      bounded128_le_words
        (Bounded128 left_middle left_low)
        (Bounded128 right_middle right_low)))
End

Definition bounded192_sub_words_def:
  bounded192_sub_words
      (Bounded192 left_high left_middle left_low)
      (Bounded192 right_high right_middle right_low) =
    if bounded192_le_words
         (Bounded192 right_high right_middle right_low)
         (Bounded192 left_high left_middle left_low)
    then
      let low_result = bounded_word64_sub_borrow left_low right_low in
      let middle_result = bounded_word64_sub_borrow_in
        left_middle right_middle (SND low_result) in
      let high_result = bounded_word64_sub_borrow_in
        left_high right_high (SND middle_result) in
      if SND high_result then NONE
      else SOME
        (Bounded192 (FST high_result)
          (FST middle_result) (FST low_result))
    else NONE
End

Definition bounded128_mul_word64_to_192_words_def:
  bounded128_mul_word64_to_192_words
      (Bounded128 left_high left_low) (right:word64) =
    let low_product = bounded_word64_mul_full_chunks22 left_low right in
    let high_product = bounded_word64_mul_full_chunks22 left_high right in
    let middle_sum = bounded_word64_add_carry
      (FST low_product) (SND high_product) F in
    let high_sum = bounded_word64_add_carry
      (FST high_product) 0w (SND middle_sum) in
    if SND high_sum then NONE
    else SOME
      (Bounded192 (FST high_sum) (FST middle_sum) (SND low_product))
End

Theorem bounded192_le_words_correct:
  bounded192_le_words left right ⇔
  bounded192_to_num left ≤ bounded192_to_num right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded192_le_words_def, bounded192_to_num_def, WORD_LO,
         bounded128_le_words_correct]
  >> Cases_on `c = c'`
  >- simp [bounded128_to_num_def]
  >> `w2n c ≠ w2n c'` by metis_tac [w2n_11]
  >> qspec_then `c` assume_tac w2n_lt
  >> qspec_then `c'` assume_tac w2n_lt
  >> qspec_then `c0` assume_tac w2n_lt
  >> qspec_then `c0'` assume_tac w2n_lt
  >> qspec_then `c1` assume_tac w2n_lt
  >> qspec_then `c1'` assume_tac w2n_lt
  >> fs [bounded128_to_num_def, bounded_word_base_def, dimword_64]
  >> Cases_on `w2n c < w2n c'`
  >> fs []
  >> `w2n c ≠ w2n c'` by metis_tac [w2n_11]
  >> `w2n c' ≤ w2n c` by fs [NOT_LESS]
  >> `w2n c' < w2n c` by metis_tac [LESS_OR_EQ]
  >> Q.PAT_X_ASSUM `c ≠ c'` kall_tac
  >> fs [NOT_LESS_EQUAL]
  >> intLib.ARITH_TAC
QED

Theorem bounded128_mul_word64_to_192_words_some:
  bounded128_mul_word64_to_192_words left right = SOME result ⇒
  bounded192_to_num result = bounded128_to_num left * w2n right
Proof
  Cases_on `left`
  >> Cases_on `result`
  >> rw [bounded128_mul_word64_to_192_words_def,
         bounded_word64_mul_full_chunks22_correct,
         bounded_word64_add_carry_correct, add_with_carry_def]
  >> fs [bounded192_to_num_def, bounded128_to_num_def,
         bounded_word_base_def, dimword_64]
  >- (mp_tac
        (Q.INST
          [`left` |-> `(c0:word64)`, `right` |-> `right`]
          bounded_word64_mul_full_chunks22_correct)
      >> mp_tac
        (Q.INST
          [`left` |-> `(c:word64)`, `right` |-> `right`]
          bounded_word64_mul_full_chunks22_correct)
      >> simp [LET_THM, bounded_word_base_eq]
      >> rpt strip_tac
      >> qspec_then
           `FST (bounded_word64_mul_full_chunks22 c0 right)`
           assume_tac w2n_lt
      >> qspec_then
           `SND (bounded_word64_mul_full_chunks22 c right)`
           assume_tac w2n_lt
      >> fs [dimword_64]
      >> `(w2n (FST (bounded_word64_mul_full_chunks22 c0 right)) +
            w2n (SND (bounded_word64_mul_full_chunks22 c right))) MOD
           18446744073709551616 =
           w2n (FST (bounded_word64_mul_full_chunks22 c0 right)) +
           w2n (SND (bounded_word64_mul_full_chunks22 c right)) -
           18446744073709551616` by
           (irule MOD_UNIQUE
            >> qexists_tac `1`
            >> simp []
            >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> mp_tac
       (Q.INST
         [`left` |-> `(c0:word64)`, `right` |-> `right`]
         bounded_word64_mul_full_chunks22_correct)
  >> mp_tac
       (Q.INST
         [`left` |-> `(c:word64)`, `right` |-> `right`]
         bounded_word64_mul_full_chunks22_correct)
  >> simp [LET_THM, bounded_word_base_eq]
  >> rpt strip_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_wide_closed_tests:
  bounded_word64_sub_borrow_in 7w 3w F = (4w,F) ∧
  bounded_word64_sub_borrow_in 7w 3w T = (3w,F) ∧
  bounded_word64_sub_borrow_in 0w 0w T = (-1w,T) ∧
  bounded192_le_words
    (Bounded192 0w 0w 3w) (Bounded192 0w 0w 7w) ∧
  ¬bounded192_le_words
    (Bounded192 0w 1w 0w) (Bounded192 0w 0w (-1w)) ∧
  bounded192_sub_words
    (Bounded192 0w 0w 10w) (Bounded192 0w 0w 3w) =
      SOME (Bounded192 0w 0w 7w) ∧
  bounded192_sub_words
    (Bounded192 1w 0w 0w) (Bounded192 0w 0w 1w) =
      SOME (Bounded192 0w (-1w) (-1w)) ∧
  bounded192_sub_words
    (Bounded192 0w 0w 3w) (Bounded192 0w 0w 7w) = NONE ∧
  bounded128_mul_word64_to_192_words
    (Bounded128 1w 0w) 2w = SOME (Bounded192 0w 2w 0w) ∧
  bounded128_mul_word64_to_192_words
    (Bounded128 (-1w) (-1w)) (-1w) =
      SOME (Bounded192 (-2w) (-1w) 1w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
