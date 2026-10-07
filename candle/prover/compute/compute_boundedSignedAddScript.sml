(*
  Checked signed accumulation for the bounded nonlinear executor.

  This theory is kept downstream of the stable signed-product layer so that
  subtraction/addition proof iteration does not rebuild the complete genuine
  input fixture or its translation.
*)
Theory compute_boundedSignedAdd
Ancestors
  compute_boundedSigned compute_bounded arithmetic words
Libs
  bossLib intLib

val _ = numLib.temp_prefer_num ();

Definition bounded128_le_words_def:
  bounded128_le_words
      (Bounded128 left_high left_low)
      (Bounded128 right_high right_low) =
    (word_lo left_high right_high ∨
     (left_high = right_high ∧ ¬word_lo right_low left_low))
End

Theorem bounded128_le_words_correct:
  bounded128_le_words left right ⇔
  bounded128_to_num left ≤ bounded128_to_num right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded128_le_words_def, bounded128_to_num_def, WORD_LO]
  >> Cases_on `c = c'`
  >- simp []
  >> `w2n c ≠ w2n c'` by metis_tac [w2n_11]
  >> qspec_then `c` assume_tac w2n_lt
  >> qspec_then `c'` assume_tac w2n_lt
  >> qspec_then `c0` assume_tac w2n_lt
  >> qspec_then `c0'` assume_tac w2n_lt
  >> fs [bounded_word_base_def, dimword_64]
  >> Cases_on `w2n c < w2n c'`
  >> fs []
  >> `w2n c ≠ w2n c'` by metis_tac [w2n_11]
  >> Q.PAT_X_ASSUM `c ≠ c'` kall_tac
  >> intLib.ARITH_TAC
QED

Definition bounded_word64_sub_borrow_def:
  bounded_word64_sub_borrow (left:word64) (right:word64) =
    (left - right, word_lo left right)
End

Theorem bounded_word64_sub_borrow_correct:
  let result = bounded_word64_sub_borrow left right in
  w2n (FST result) + w2n right =
    w2n left +
      bounded_word_base * if SND result then 1 else 0
Proof
  rw [bounded_word64_sub_borrow_def, LET_THM, WORD_LO]
  >- (once_rewrite_tac [GSYM WORD_NEG_MUL]
      >> once_rewrite_tac [GSYM word_sub_def]
      >> Cases_on `left`
      >> Cases_on `right`
      >> fs [word_sub_def, word_add_n2w, word_2comp_n2w,
             w2n_n2w, bounded_word_base_def, dimword_64]
      >> intLib.ARITH_TAC)
  >> once_rewrite_tac [GSYM WORD_NEG_MUL]
  >> once_rewrite_tac [GSYM word_sub_def]
  >> simp [word_sub_w2n, WORD_LS]
QED

Definition bounded128_sub_words_def:
  bounded128_sub_words
      (Bounded128 left_high left_low)
      (Bounded128 right_high right_low) =
    if bounded128_le_words
         (Bounded128 right_high right_low)
         (Bounded128 left_high left_low)
    then
      let low_result = bounded_word64_sub_borrow left_low right_low in
      let borrowed_high =
        if SND low_result then right_high + 1w else right_high in
      SOME (Bounded128 (left_high - borrowed_high) (FST low_result))
    else NONE
End

Definition bounded128_sub_def:
  bounded128_sub left right =
    if bounded128_to_num right ≤ bounded128_to_num left then
      bounded128_of_num
        (bounded128_to_num left - bounded128_to_num right)
    else NONE
End

Theorem bounded128_sub_words_none:
  bounded128_sub_words left right = NONE ⇔
  bounded128_to_num left < bounded128_to_num right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp [bounded128_sub_words_def, bounded128_le_words_correct,
           NOT_LESS_EQUAL]
QED

Theorem bounded128_sub_words_some:
  bounded128_sub_words left right = SOME result ⇒
  bounded128_to_num result =
    bounded128_to_num left - bounded128_to_num right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [bounded128_sub_words_def, bounded128_le_words_correct, LET_THM]
  >> mp_tac
       (Q.INST [`left` |-> `(c0:word64)`, `right` |-> `(c0':word64)`]
          bounded_word64_sub_borrow_correct)
  >> rw [bounded_word64_sub_borrow_def, LET_THM]
  >- (fs [bounded_word64_sub_borrow_def, WORD_LO,
          bounded128_to_num_def, bounded_word_base_eq]
      >> qspec_then `c0` assume_tac w2n_lt
      >> qspec_then `c0'` assume_tac w2n_lt
      >> `w2n c' < w2n c` by
           (fs [dimword_64] >> intLib.ARITH_TAC)
      >> qspec_then `c` assume_tac w2n_lt
      >> qspec_then `c'` assume_tac w2n_lt
      >> `w2n c' + 1 < 18446744073709551616` by
           (fs [dimword_64] >> intLib.ARITH_TAC)
      >> `c' + 1w = (n2w (w2n c' + 1):word64)` by
           metis_tac [word_add_n2w, n2w_w2n]
      >> `w2n (c' + 1w) = w2n c' + 1` by
           fs [w2n_n2w, dimword_64]
      >> `c' + 1w ≤₊ c` by fs [WORD_LS]
      >> mp_tac
           (Q.INST
              [`left` |-> `(c:word64)`,
               `right` |-> `(c' + 1w:word64)`]
              bounded_word64_sub_borrow_correct)
      >> rw [bounded_word64_sub_borrow_def, LET_THM]
      >> fs [WORD_LO, WORD_LS, w2n_n2w, dimword_64]
      >> intLib.ARITH_TAC)
  >> fs [bounded_word64_sub_borrow_def, WORD_LO,
         bounded128_to_num_def, bounded_word_base_eq]
  >> qspec_then `c0` assume_tac w2n_lt
  >> qspec_then `c0'` assume_tac w2n_lt
  >> `w2n c' ≤ w2n c` by
       (fs [dimword_64] >> intLib.ARITH_TAC)
  >> `c' ≤₊ c` by fs [WORD_LS]
  >> mp_tac
       (Q.INST [`left` |-> `(c:word64)`, `right` |-> `(c':word64)`]
          bounded_word64_sub_borrow_correct)
  >> rw [bounded_word64_sub_borrow_def, LET_THM]
  >> fs [WORD_LO, WORD_LS]
QED

Theorem bounded128_sub_words_total:
  bounded128_to_num right ≤ bounded128_to_num left ⇒
  ∃result. bounded128_sub_words left right = SOME result
Proof
  strip_tac
  >> Cases_on `bounded128_sub_words left right`
  >> fs [bounded128_sub_words_none]
QED

(* Signed accumulation keeps sign/magnitude canonical.  Equal signs use the
   existing checked carry chain and retain its explicit overflow result.
   Opposite signs subtract the smaller magnitude from the larger one. *)
Definition bounded_signed128_add_def:
  bounded_signed128_add
      (BoundedSigned128 left_negative left_magnitude)
      (BoundedSigned128 right_negative right_magnitude) =
    if left_negative = right_negative then
      case bounded128_add_words left_magnitude right_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed128_make left_negative magnitude)
    else if bounded128_le_words left_magnitude right_magnitude then
      case bounded128_sub_words right_magnitude left_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed128_make right_negative magnitude)
    else
      case bounded128_sub_words left_magnitude right_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed128_make left_negative magnitude)
End

Theorem bounded_signed128_make_option_normalized:
  (case source of
   | NONE => NONE
   | SOME magnitude => SOME (bounded_signed128_make negative magnitude)) =
    SOME result ⇒
  bounded_signed128_normalized result
Proof
  Cases_on `source`
  >> fs []
  >> metis_tac [bounded_signed128_make_normalized]
QED

Theorem bounded_signed128_add_normalized:
  bounded_signed128_add left right = SOME result ⇒
  bounded_signed128_normalized result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed128_add_def]
  >> metis_tac [bounded_signed128_make_option_normalized]
QED

Theorem bounded_signed128_add_mixed_tests:
  bounded_signed128_add
      (BoundedSigned128 F (Bounded128 0w 5w))
      (BoundedSigned128 T (Bounded128 0w 3w)) =
    SOME (BoundedSigned128 F (Bounded128 0w 2w)) ∧
  bounded_signed128_add
      (BoundedSigned128 T (Bounded128 0w 5w))
      (BoundedSigned128 F (Bounded128 0w 3w)) =
    SOME (BoundedSigned128 T (Bounded128 0w 2w)) ∧
  bounded_signed128_add
      (BoundedSigned128 T (Bounded128 0w 5w))
      (BoundedSigned128 F (Bounded128 0w 5w)) =
    SOME (BoundedSigned128 F (Bounded128 0w 0w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_signed128_add_same_sign_test:
  bounded_signed128_add
      (BoundedSigned128 T (Bounded128 0w 5w))
      (BoundedSigned128 T (Bounded128 0w 3w)) =
    SOME (BoundedSigned128 T (Bounded128 0w 8w))
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
