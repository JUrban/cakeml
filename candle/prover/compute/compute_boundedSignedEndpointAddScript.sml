(*****************************************************************************
 * Exact stored-endpoint negation and addition.
 *
 * Addition widens each one-word endpoint to the existing checked signed
 * 128-bit accumulator and narrows only after exact accumulation.  Overflow
 * at either stage remains explicit.
 *****************************************************************************)
Theory compute_boundedSignedEndpointAdd
Ancestors
  compute_boundedSignedEndpoint compute_boundedSignedAdd
  compute_boundedSigned compute_bounded
Libs
  bossLib intLib

Definition bounded_signed64_neg_def:
  bounded_signed64_neg (BoundedSigned64 negative magnitude) =
    bounded_signed64_make (¬negative) magnitude
End

Definition bounded_signed64_add_def:
  bounded_signed64_add left right =
    case bounded_signed128_add
           (bounded_signed64_widen128 left)
           (bounded_signed64_widen128 right) of
    | NONE => NONE
    | SOME wide => bounded_signed128_narrow64 wide
End

Theorem bounded_signed128_make_value:
  bounded_signed128_to_int (bounded_signed128_make negative magnitude) =
  (if negative then -&(bounded128_to_num magnitude)
   else &(bounded128_to_num magnitude))
Proof
  Cases_on `negative`
  >> Cases_on `bounded128_is_zero magnitude`
  >> fs [bounded_signed128_make_def, bounded_signed128_to_int_def,
         bounded128_is_zero_iff]
QED

Theorem bounded_signed128_add_value:
  bounded_signed128_add left right = SOME result ⇒
  bounded_signed128_to_int result =
    bounded_signed128_to_int left + bounded_signed128_to_int right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_signed128_add
          (BoundedSigned128 left_negative left_magnitude)
          (BoundedSigned128 right_negative right_magnitude) = SOME result`
  >> Cases_on `left_negative = right_negative`
  >- (fs []
      >> rw [bounded_signed128_add_def]
      >> Cases_on `bounded128_add_words left_magnitude right_magnitude`
      >> gvs [bounded128_add_words_refines,
              bounded_signed128_make_value,
              bounded_signed128_to_int_def]
      >> imp_res_tac bounded128_add_some
      >> Cases_on `left_negative`
      >> fs []
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded128_le_words left_magnitude right_magnitude`
  >> rw [bounded_signed128_add_def]
  >- (Cases_on `bounded128_sub_words right_magnitude left_magnitude`
      >> gvs []
      >> imp_res_tac bounded128_sub_words_some
      >> Cases_on `left_negative`
      >> Cases_on `right_negative`
      >> fs [bounded_signed128_make_value,
             bounded_signed128_to_int_def,
             bounded128_le_words_correct]
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded128_sub_words left_magnitude right_magnitude`
  >> gvs []
  >> imp_res_tac bounded128_sub_words_some
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [bounded_signed128_make_value,
         bounded_signed128_to_int_def,
         bounded128_le_words_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_neg_value:
  bounded_signed64_to_int (bounded_signed64_neg value) =
  -bounded_signed64_to_int value
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `magnitude = 0w`
  >> simp [bounded_signed64_neg_def, bounded_signed64_make_value,
           bounded_signed64_to_int_def, wordsTheory.w2n_eq_0]
QED

Theorem bounded_signed64_neg_normalized:
  bounded_signed64_normalized (bounded_signed64_neg value)
Proof
  Cases_on `value`
  >> simp [bounded_signed64_neg_def, bounded_signed64_make_normalized]
QED

Theorem bounded_signed64_add_value:
  bounded_signed64_add left right = SOME result ⇒
  bounded_signed64_normalized result ∧
  bounded_signed64_to_int result =
    bounded_signed64_to_int left + bounded_signed64_to_int right
Proof
  rw [bounded_signed64_add_def]
  >> Cases_on
       `bounded_signed128_add
          (bounded_signed64_widen128 left)
          (bounded_signed64_widen128 right)`
  >> gvs []
  >> imp_res_tac bounded_signed128_narrow64_some
  >> imp_res_tac bounded_signed128_add_value
  >> fs [bounded_signed64_widen128_value]
QED

Theorem bounded_signed64_add_closed_tests:
  bounded_signed64_add
    (BoundedSigned64 F 7w) (BoundedSigned64 T 3w) =
      SOME (BoundedSigned64 F 4w) ∧
  bounded_signed64_add
    (BoundedSigned64 T 7w) (BoundedSigned64 F 3w) =
      SOME (BoundedSigned64 T 4w) ∧
  bounded_signed64_add
    (BoundedSigned64 T 7w) (BoundedSigned64 F 7w) =
      SOME (BoundedSigned64 F 0w) ∧
  bounded_signed64_add
    (BoundedSigned64 F (-1w)) (BoundedSigned64 F 1w) = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
