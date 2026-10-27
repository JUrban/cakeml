(*****************************************************************************
 * Signed word-only 192-bit arithmetic and the two Taylor rounding scales.
 *
 * This DEVELOPMENT layer supplies the concrete signed accumulator needed by
 * the compact nonlinear checker.  Every operation is total and reports
 * overflow through option.  General refinement to the mathematical integer
 * and directed-rounding contracts remains a release obligation; the closed
 * tests below exercise sign cancellation, overflow, limb shifts, and both
 * directed branches used by Taylor completion.
 *****************************************************************************)
Theory compute_boundedWideSigned
Ancestors
  compute_boundedWide compute_boundedSignedEndpoint
Libs
  bossLib preamble intLib

Datatype:
  bounded_signed192 = BoundedSigned192 bool bounded192
End

Definition bounded192_is_zero_def:
  bounded192_is_zero (Bounded192 high middle low) =
    (high = 0w ∧ middle = 0w ∧ low = 0w)
End

Definition bounded_signed192_to_int_def:
  bounded_signed192_to_int (BoundedSigned192 negative magnitude) =
    if negative then -&(bounded192_to_num magnitude)
    else &(bounded192_to_num magnitude)
End

Definition bounded_signed192_make_def:
  bounded_signed192_make negative magnitude =
    BoundedSigned192 (negative ∧ ¬bounded192_is_zero magnitude) magnitude
End

Definition bounded_signed192_normalized_def:
  bounded_signed192_normalized (BoundedSigned192 negative magnitude) ⇔
    ¬negative ∨ ¬bounded192_is_zero magnitude
End

Definition bounded_signed192_add_def:
  bounded_signed192_add
      (BoundedSigned192 left_negative left_magnitude)
      (BoundedSigned192 right_negative right_magnitude) =
    if left_negative = right_negative then
      case bounded192_add_words left_magnitude right_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed192_make left_negative magnitude)
    else if bounded192_le_words left_magnitude right_magnitude then
      case bounded192_sub_words right_magnitude left_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed192_make right_negative magnitude)
    else
      case bounded192_sub_words left_magnitude right_magnitude of
      | NONE => NONE
      | SOME magnitude =>
          SOME (bounded_signed192_make left_negative magnitude)
End

(* Multiplication by 2^81 = 2 * (2^40)^2 for a stored endpoint. *)
Definition bounded_signed64_scale81_def:
  bounded_signed64_scale81 (BoundedSigned64 negative magnitude) =
    bounded_signed192_make negative
      (Bounded192 (magnitude >>> 47) (magnitude << 17) 0w)
End

(* Multiplication by 2^41 = 2 * 2^40 for the linear Taylor term. *)
Definition bounded128_scale41_def:
  bounded128_scale41 (Bounded128 high low) =
    Bounded192
      (high >>> 23)
      ((low >>> 23) + (high << 41))
      (low << 41)
End

(* Quotient and remainder discriminator for division by 2^81. *)
Definition bounded192_shift_floor81_words_def:
  bounded192_shift_floor81_words (Bounded192 high middle low) =
    Bounded128
      (high >>> 17)
      ((middle >>> 17) + (high << 47))
End

Definition bounded192_low81_nonzero_def:
  bounded192_low81_nonzero (Bounded192 high middle low) =
    (low ≠ 0w ∨ word_and middle 131071w ≠ 0w)
End

Definition bounded_signed128_narrow64_option_def:
  bounded_signed128_narrow64_option negative source =
    case source of
    | NONE => NONE
    | SOME magnitude =>
        bounded_signed128_narrow64
          (bounded_signed128_make negative magnitude)
End

Definition bounded_signed192_shift_floor81_64_def:
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 negative magnitude) =
    let quotient = bounded192_shift_floor81_words magnitude in
    if negative ∧ bounded192_low81_nonzero magnitude then
      bounded_signed128_narrow64_option T
        (bounded128_add_words quotient (Bounded128 0w 1w))
    else
      bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Definition bounded_signed192_shift_ceil81_64_def:
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 negative magnitude) =
    let quotient = bounded192_shift_floor81_words magnitude in
    if ¬negative ∧ bounded192_low81_nonzero magnitude then
      bounded_signed128_narrow64_option F
        (bounded128_add_words quotient (Bounded128 0w 1w))
    else
      bounded_signed128_narrow64
        (bounded_signed128_make negative quotient)
End

Theorem bounded192_is_zero_iff:
  bounded192_is_zero magnitude ⇔ bounded192_to_num magnitude = 0
Proof
  Cases_on `magnitude`
  >> simp [bounded192_is_zero_def,
           compute_boundedTheory.bounded192_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           wordsTheory.w2n_eq_0]
QED

Theorem bounded_signed192_make_value:
  bounded_signed192_to_int (bounded_signed192_make negative magnitude) =
  (if negative then -&(bounded192_to_num magnitude)
   else &(bounded192_to_num magnitude))
Proof
  Cases_on `negative`
  >> Cases_on `bounded192_is_zero magnitude`
  >> fs [bounded_signed192_make_def, bounded_signed192_to_int_def,
         bounded192_is_zero_iff]
QED

Theorem bounded_signed192_make_normalized:
  bounded_signed192_normalized
    (bounded_signed192_make negative magnitude)
Proof
  Cases_on `negative`
  >> simp [bounded_signed192_make_def, bounded_signed192_normalized_def]
QED

Theorem bounded_signed192_make_option_normalized:
  (case source of
   | NONE => NONE
   | SOME magnitude => SOME (bounded_signed192_make negative magnitude)) =
    SOME result ⇒
  bounded_signed192_normalized result
Proof
  Cases_on `source`
  >> fs []
  >> metis_tac [bounded_signed192_make_normalized]
QED

Theorem bounded_signed192_add_normalized:
  bounded_signed192_add left right = SOME result ⇒
  bounded_signed192_normalized result
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw [bounded_signed192_add_def]
  >> metis_tac [bounded_signed192_make_option_normalized]
QED

Theorem bounded_signed192_add_value:
  bounded_signed192_add left right = SOME result ⇒
  bounded_signed192_to_int result =
    bounded_signed192_to_int left + bounded_signed192_to_int right
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rename1
       `bounded_signed192_add
          (BoundedSigned192 left_negative left_magnitude)
          (BoundedSigned192 right_negative right_magnitude) = SOME result`
  >> Cases_on `left_negative = right_negative`
  >- (fs []
      >> rw [bounded_signed192_add_def]
      >> Cases_on `bounded192_add_words left_magnitude right_magnitude`
      >> gvs [compute_boundedTheory.bounded192_add_words_refines,
              bounded_signed192_make_value,
              bounded_signed192_to_int_def]
      >> imp_res_tac compute_boundedTheory.bounded192_add_some
      >> Cases_on `left_negative`
      >> fs []
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded192_le_words left_magnitude right_magnitude`
  >> rw [bounded_signed192_add_def]
  >- (Cases_on `bounded192_sub_words right_magnitude left_magnitude`
      >> gvs []
      >> imp_res_tac compute_boundedWideTheory.bounded192_sub_words_some
      >> Cases_on `left_negative`
      >> Cases_on `right_negative`
      >> fs [bounded_signed192_make_value,
             bounded_signed192_to_int_def,
             compute_boundedWideTheory.bounded192_le_words_correct]
      >> intLib.ARITH_TAC)
  >> Cases_on `bounded192_sub_words left_magnitude right_magnitude`
  >> gvs []
  >> imp_res_tac compute_boundedWideTheory.bounded192_sub_words_some
  >> Cases_on `left_negative`
  >> Cases_on `right_negative`
  >> fs [bounded_signed192_make_value,
         bounded_signed192_to_int_def,
         compute_boundedWideTheory.bounded192_le_words_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_scale81_num_identity:
  n < 18446744073709551616 ==>
  340282366920938463463374607431768211456 *
      (n DIV 140737488355328) +
    18446744073709551616 *
      ((131072 * n) MOD 18446744073709551616) =
    2417851639229258349412352 * n
Proof
  strip_tac
  >> qabbrev_tac `q = n DIV 140737488355328`
  >> qabbrev_tac `r = n MOD 140737488355328`
  >> `r < 140737488355328` by
       (qunabbrev_tac `r` >> simp [])
  >> `r + 140737488355328 * q = n` by
       (qunabbrev_tac `r`
        >> qunabbrev_tac `q`
        >> irule compute_boundedTheory.bounded_division_reconstruct
        >> simp [])
  >> `131072 * r < 18446744073709551616` by intLib.ARITH_TAC
  >> `131072 * n =
        q * 18446744073709551616 + 131072 * r` by intLib.ARITH_TAC
  >> `(131072 * n) MOD 18446744073709551616 = 131072 * r` by
       (qpat_x_assum
          `131072 * n =
             q * 18446744073709551616 + 131072 * r`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `q`
        >> simp [])
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_scale81_value:
  bounded_signed192_to_int (bounded_signed64_scale81 value) =
    (&2417851639229258349412352:int) *
      bounded_signed64_to_int value
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `magnitude`
  >> simp [bounded_signed64_scale81_def,
           bounded_signed192_make_value,
           bounded_signed64_to_int_def,
           compute_boundedTheory.bounded192_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           w2n_lsr, word_lsl_n2w, dimword_64]
  >> fs [dimword_64]
  >> assume_tac (Q.INST [`n` |-> `n`] bounded_scale81_num_identity)
  >> fs []
  >> PURE_REWRITE_TAC [GSYM integerTheory.INT_OF_NUM_MUL]
  >> INT_RING_TAC
QED

Theorem bounded_scale41_num_identity:
  high < 18446744073709551616 /\
  low < 18446744073709551616 ==>
  340282366920938463463374607431768211456 *
      (high DIV 8388608) +
    ((2199023255552 * low) MOD 18446744073709551616 +
     18446744073709551616 *
       (((2199023255552 * high) MOD 18446744073709551616 +
         low DIV 8388608) MOD 18446744073709551616)) =
  2199023255552 *
    (18446744073709551616 * high + low)
Proof
  strip_tac
  >> qabbrev_tac `high_q = high DIV 8388608`
  >> qabbrev_tac `high_r = high MOD 8388608`
  >> qabbrev_tac `low_q = low DIV 8388608`
  >> qabbrev_tac `low_r = low MOD 8388608`
  >> `high_r < 8388608 /\ low_r < 8388608` by
       (qunabbrev_tac `high_r`
        >> qunabbrev_tac `low_r`
        >> simp [])
  >> `high_q < 2199023255552 /\ low_q < 2199023255552` by
       (qunabbrev_tac `high_q`
        >> qunabbrev_tac `low_q`
        >> simp [DIV_LT_X])
  >> `high_r + 8388608 * high_q = high /\
      low_r + 8388608 * low_q = low` by
       (conj_tac
        >> qunabbrev_tac `high_r`
        >> qunabbrev_tac `high_q`
        >> qunabbrev_tac `low_r`
        >> qunabbrev_tac `low_q`
        >> irule compute_boundedTheory.bounded_division_reconstruct
        >> simp [])
  >> `2199023255552 * high =
        high_q * 18446744073709551616 +
          2199023255552 * high_r /\
      2199023255552 * low =
        low_q * 18446744073709551616 +
          2199023255552 * low_r` by intLib.ARITH_TAC
  >> `2199023255552 * high_r < 18446744073709551616 /\
      2199023255552 * low_r < 18446744073709551616 /\
      2199023255552 * high_r + low_q < 18446744073709551616` by
       intLib.ARITH_TAC
  >> `(2199023255552 * high) MOD 18446744073709551616 =
        2199023255552 * high_r` by
       (qpat_x_assum `2199023255552 * high = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `high_q`
        >> simp [])
  >> `(2199023255552 * low) MOD 18446744073709551616 =
        2199023255552 * low_r` by
       (qpat_x_assum `2199023255552 * low = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `low_q`
        >> simp [])
  >> asm_rewrite_tac []
  >> simp [LESS_MOD]
  >> intLib.ARITH_TAC
QED

Theorem bounded128_scale41_value:
  bounded192_to_num (bounded128_scale41 value) =
    2199023255552 * bounded128_to_num value
Proof
  Cases_on `value`
  >> rename1 `Bounded128 high low`
  >> Cases_on `high`
  >> Cases_on `low`
  >> simp [bounded128_scale41_def,
           compute_boundedTheory.bounded128_to_num_def,
           compute_boundedTheory.bounded192_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           w2n_lsr, word_lsl_n2w, word_add_n2w, dimword_64]
  >> fs [dimword_64]
  >> `((n2w n'):word64) >>> 23 = n2w (n' DIV 8388608)` by
       (mp_tac
          (Q.SPECL [`n'`, `23`]
            (n2w_DIV |> INST_TYPE [alpha |-> ``:64``]))
        >> simp [dimword_64])
  >> asm_rewrite_tac []
  >> simp [word_add_n2w, dimword_64]
  >> assume_tac
       (Q.INST [`high` |-> `n`, `low` |-> `n'`]
          bounded_scale41_num_identity)
  >> fs []
QED

Theorem bounded_word64_shift_pair17_correct:
  w2n (((middle:word64) >>> 17) + ((high:word64) << 47)) +
    bounded_word_base * w2n (high >>> 17) =
  (w2n middle + bounded_word_base * w2n high) DIV 131072
Proof
  Cases_on `high`
  >> Cases_on `middle`
  >> fs [dimword_64]
  >> `((n2w n'):word64) >>> 17 = n2w (n' DIV 131072)` by
       (mp_tac
          (Q.SPECL [`n'`, `17`]
            (n2w_DIV |> INST_TYPE [alpha |-> ``:64``]))
        >> simp [dimword_64])
  >> asm_rewrite_tac []
  >> simp [compute_boundedTheory.bounded_word_base_eq,
           w2n_lsr, word_lsl_n2w,
           word_add_n2w, w2n_n2w, dimword_64]
  >> qabbrev_tac `q = n DIV 131072`
  >> qabbrev_tac `r = n MOD 131072`
  >> qabbrev_tac `q' = n' DIV 131072`
  >> qabbrev_tac `r' = n' MOD 131072`
  >> `r < 131072 /\ r' < 131072` by
       (qunabbrev_tac `r`
        >> qunabbrev_tac `r'`
        >> simp [])
  >> `q < 140737488355328 /\ q' < 140737488355328` by
       (qunabbrev_tac `q`
        >> qunabbrev_tac `q'`
        >> simp [DIV_LT_X])
  >> `r + 131072 * q = n /\ r' + 131072 * q' = n'` by
       (conj_tac
        >> qunabbrev_tac `r`
        >> qunabbrev_tac `q`
        >> qunabbrev_tac `r'`
        >> qunabbrev_tac `q'`
        >> irule compute_boundedTheory.bounded_division_reconstruct
        >> simp [])
  >> `140737488355328 * n + q' =
      q * 18446744073709551616 + (140737488355328 * r + q')` by
       intLib.ARITH_TAC
  >> `140737488355328 * r + q' < 18446744073709551616` by
       intLib.ARITH_TAC
  >> `(140737488355328 * n + q') MOD 18446744073709551616 =
      140737488355328 * r + q'` by
       (qpat_x_assum
          `140737488355328 * n + q' = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `q`
        >> simp [])
  >> `18446744073709551616 * n + n' =
      (18446744073709551616 * q + 140737488355328 * r + q') *
        131072 + r'` by intLib.ARITH_TAC
  >> `(18446744073709551616 * n + n') DIV 131072 =
      18446744073709551616 * q + 140737488355328 * r + q'` by
       (qpat_x_assum
          `18446744073709551616 * n + n' = _`
          (fn th => once_rewrite_tac [th])
        >> irule DIV_UNIQUE
        >> qexists_tac `r'`
        >> simp [])
  >> asm_rewrite_tac []
  >> CONV_TAC (EQT_INTRO o Grobner.NUM_RING)
QED

Theorem bounded192_shift_floor81_words_correct:
  bounded128_to_num (bounded192_shift_floor81_words value) =
    bounded192_to_num value DIV 2417851639229258349412352
Proof
  Cases_on `value`
  >> rename1 `Bounded192 high middle low`
  >> rw [bounded192_shift_floor81_words_def,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded192_to_num_def]
  >> once_rewrite_tac [WORD_ADD_COMM]
  >> rw [bounded_word64_shift_pair17_correct]
  >> simp [compute_boundedTheory.bounded_word_base_eq]
  >> qabbrev_tac
       `pair = 18446744073709551616 * w2n high + w2n middle`
  >> qabbrev_tac
       `whole_value =
          340282366920938463463374607431768211456 * w2n high +
          (w2n low + 18446744073709551616 * w2n middle)`
  >> `w2n low < 18446744073709551616` by
       (qspec_then `low` assume_tac w2n_lt >> fs [dimword_64])
  >> `whole_value = w2n low + 18446744073709551616 * pair` by
       (qunabbrev_tac `whole_value`
        >> qunabbrev_tac `pair`
        >> CONV_TAC (EQT_INTRO o Grobner.NUM_RING))
  >> `whole_value DIV 18446744073709551616 = pair` by
       (qpat_x_assum
          `whole_value = w2n low + 18446744073709551616 * pair`
          (fn th => rewrite_tac [th])
        >> `w2n low + 18446744073709551616 * pair =
            pair * 18446744073709551616 + w2n low` by
             CONV_TAC (EQT_INTRO o Grobner.NUM_RING)
        >> asm_rewrite_tac []
        >> match_mp_tac DIV_MULT
        >> asm_rewrite_tac [])
  >> `(whole_value DIV 18446744073709551616) DIV 131072 =
      whole_value DIV (18446744073709551616 * 131072)` by
       (mp_tac
          (Q.SPECL [`18446744073709551616`, `131072`]
             DIV_DIV_DIV_MULT)
        >> impl_tac >- EVAL_TAC
        >> disch_then (qspec_then `whole_value` MATCH_ACCEPT_TAC))
  >> qpat_x_assum
       `whole_value DIV 18446744073709551616 = pair`
       (fn base_th =>
         qpat_x_assum
           `whole_value DIV 18446744073709551616 DIV 131072 = _`
           (fn division_th =>
             MATCH_ACCEPT_TAC
               (REWRITE_RULE
                 [base_th,
                  EQT_ELIM
                    (EVAL
                      ``((18446744073709551616:num) * 131072 =
                          2417851639229258349412352)``)]
                 division_th)))
QED

Theorem bounded_word64_low17_nonzero_correct:
  word_and (value:word64) 131071w ≠ 0w <=>
  w2n value MOD 131072 ≠ 0
Proof
  mp_tac
    (Q.SPECL [`17`, `w2n (value:word64)`]
      (WORD_AND_EXP_SUB1 |> INST_TYPE [alpha |-> ``:64``]))
  >> simp [n2w_w2n, wordsTheory.w2n_eq_0,
           w2n_n2w, dimword_64]
  >> strip_tac
  >> `w2n (value:word64) MOD 131072 < 18446744073709551616` by
       (irule LESS_TRANS
        >> qexists_tac `131072`
        >> simp [])
  >> simp []
QED

Theorem bounded192_low81_nonzero_correct:
  bounded192_low81_nonzero magnitude <=>
  bounded192_to_num magnitude MOD 2417851639229258349412352 ≠ 0
Proof
  Cases_on `magnitude`
  >> rename1 `Bounded192 high middle low`
  >> qabbrev_tac `q = w2n middle DIV 131072`
  >> qabbrev_tac `r = w2n middle MOD 131072`
  >> `r < 131072` by (qunabbrev_tac `r` >> simp [])
  >> `w2n low < 18446744073709551616` by
       (qspec_then `low` assume_tac w2n_lt >> fs [dimword_64])
  >> `w2n middle = r + 131072 * q` by
       (qunabbrev_tac `r`
        >> qunabbrev_tac `q`
        >> once_rewrite_tac [EQ_SYM_EQ]
        >> irule compute_boundedTheory.bounded_division_reconstruct
        >> simp [])
  >> `w2n low + 18446744073709551616 * r <
      2417851639229258349412352` by intLib.ARITH_TAC
  >> `w2n low + 18446744073709551616 * w2n middle +
       18446744073709551616 * 18446744073709551616 * w2n high =
      (140737488355328 * w2n high + q) *
        2417851639229258349412352 +
      (w2n low + 18446744073709551616 * r)` by intLib.ARITH_TAC
  >> `(w2n low + 18446744073709551616 * w2n middle +
        18446744073709551616 * 18446744073709551616 * w2n high) MOD
       2417851639229258349412352 =
      w2n low + 18446744073709551616 * r` by
       (qpat_x_assum
          `w2n low + 18446744073709551616 * w2n middle + _ = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `140737488355328 * w2n high + q`
        >> simp [])
  >> simp_tac bool_ss
       [bounded192_low81_nonzero_def,
        compute_boundedTheory.bounded192_to_num_def,
        compute_boundedTheory.bounded_word_base_eq]
  >> qpat_x_assum
       `(w2n low + 18446744073709551616 * w2n middle + _) MOD _ = _`
       (fn th => rewrite_tac [th])
  >> Cases_on `low = 0w`
  >> qunabbrev_tac `r`
  >> fs [bounded_word64_low17_nonzero_correct,
         wordsTheory.w2n_eq_0]
QED

Theorem bounded_signed192_shift_floor81_64_value:
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 negative magnitude) = SOME result ==>
  bounded_signed64_to_int result =
    if negative then
      -&(bounded192_to_num magnitude DIV 2417851639229258349412352 +
         if bounded192_to_num magnitude MOD 2417851639229258349412352 = 0
         then 0 else 1)
    else
      &(bounded192_to_num magnitude DIV 2417851639229258349412352)
Proof
  rw [bounded_signed192_shift_floor81_64_def, LET_THM]
  >> every_case_tac
  >> gvs [bounded_signed128_narrow64_option_def,
          bounded192_low81_nonzero_correct,
          compute_boundedTheory.bounded128_add_words_refines]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_some
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> fs [compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
         bounded192_shift_floor81_words_correct,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded_word_base_eq]
QED

Theorem bounded_signed192_shift_ceil81_64_value:
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 negative magnitude) = SOME result ==>
  bounded_signed64_to_int result =
    if negative then
      -&(bounded192_to_num magnitude DIV 2417851639229258349412352)
    else
      &(bounded192_to_num magnitude DIV 2417851639229258349412352 +
         if bounded192_to_num magnitude MOD 2417851639229258349412352 = 0
         then 0 else 1)
Proof
  rw [bounded_signed192_shift_ceil81_64_def, LET_THM]
  >> every_case_tac
  >> gvs [bounded_signed128_narrow64_option_def,
          bounded192_low81_nonzero_correct,
          compute_boundedTheory.bounded128_add_words_refines]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_some
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> fs [compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
         bounded192_shift_floor81_words_correct,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded_word_base_eq]
QED

Theorem bounded_div_floor81_scaled_le:
  (value DIV 2417851639229258349412352) *
      2417851639229258349412352 <= value
Proof
  simp [GSYM arithmeticTheory.X_LE_DIV]
QED

Theorem bounded_div_ceil81_scaled_ge:
  value <=
    (value DIV 2417851639229258349412352 +
       if value MOD 2417851639229258349412352 = 0 then 0 else 1) *
      2417851639229258349412352
Proof
  mp_tac
    (Q.SPEC `2417851639229258349412352` arithmeticTheory.DIVISION)
  >> simp []
  >> disch_then (qspec_then `value` strip_assume_tac)
  >> Cases_on `value MOD 2417851639229258349412352 = 0`
  >> fs [arithmeticTheory.LEFT_ADD_DISTRIB]
  >> qpat_x_assum `value = _` (fn th => once_rewrite_tac [th])
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed192_shift_floor81_64_lower_bound:
  bounded_signed192_shift_floor81_64 source = SOME result ==>
  (&2417851639229258349412352:int) *
      bounded_signed64_to_int result <=
    bounded_signed192_to_int source
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> strip_tac
  >> imp_res_tac bounded_signed192_shift_floor81_64_value
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          bounded_div_floor81_scaled_le)
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          bounded_div_ceil81_scaled_ge)
  >> Cases_on `negative`
  >> fs [bounded_signed192_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_signed192_shift_ceil81_64_upper_bound:
  bounded_signed192_shift_ceil81_64 source = SOME result ==>
  bounded_signed192_to_int source <=
    (&2417851639229258349412352:int) *
      bounded_signed64_to_int result
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned192 negative magnitude`
  >> strip_tac
  >> imp_res_tac bounded_signed192_shift_ceil81_64_value
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          bounded_div_floor81_scaled_le)
  >> assume_tac
       (Q.INST [`value` |-> `bounded192_to_num magnitude`]
          bounded_div_ceil81_scaled_ge)
  >> Cases_on `negative`
  >> fs [bounded_signed192_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_wide_signed_closed_tests:
  bounded_signed192_add
      (BoundedSigned192 F (Bounded192 0w 0w 7w))
      (BoundedSigned192 T (Bounded192 0w 0w 3w)) =
    SOME (BoundedSigned192 F (Bounded192 0w 0w 4w)) ∧
  bounded_signed192_add
      (BoundedSigned192 T (Bounded192 0w 0w 7w))
      (BoundedSigned192 F (Bounded192 0w 0w 7w)) =
    SOME (BoundedSigned192 F (Bounded192 0w 0w 0w)) ∧
  bounded_signed192_add
      (BoundedSigned192 F (Bounded192 (-1w) (-1w) (-1w)))
      (BoundedSigned192 F (Bounded192 0w 0w 1w)) = NONE ∧
  bounded_signed64_scale81 (BoundedSigned64 F 3w) =
    BoundedSigned192 F (Bounded192 0w 393216w 0w) ∧
  bounded128_scale41 (Bounded128 0w 3w) =
    Bounded192 0w 0w 6597069766656w ∧
  bounded192_shift_floor81_words (Bounded192 0w 393216w 0w) =
    Bounded128 0w 3w ∧
  ¬bounded192_low81_nonzero (Bounded192 0w 393216w 0w) ∧
  bounded192_low81_nonzero (Bounded192 0w 393216w 1w) ∧
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 F (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 F 3w) ∧
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 F (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 F 4w) ∧
  bounded_signed192_shift_floor81_64
      (BoundedSigned192 T (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 T 4w) ∧
  bounded_signed192_shift_ceil81_64
      (BoundedSigned192 T (Bounded192 0w 393216w 1w)) =
    SOME (BoundedSigned64 T 3w)
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
