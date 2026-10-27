(*****************************************************************************
 * Directed-rounding facts for completed Taylor gradient rows.
 *
 * This proof-only sidecar preserves the executable Taylor-gradient identity.
 *****************************************************************************)
Theory compute_boundedTaylorGradientBounds
Ancestors
  compute_boundedTaylorGradient
Libs
  bossLib preamble intLib

Theorem bounded_scale40_num_identity:
  n < 18446744073709551616 ==>
  18446744073709551616 * (n DIV 16777216) +
    (1099511627776 * n) MOD 18446744073709551616 =
  1099511627776 * n
Proof
  strip_tac
  >> qabbrev_tac `q = n DIV 16777216`
  >> qabbrev_tac `r = n MOD 16777216`
  >> `r < 16777216` by (qunabbrev_tac `r` >> simp [])
  >> `r + 16777216 * q = n` by
       (qunabbrev_tac `r`
        >> qunabbrev_tac `q`
        >> irule compute_boundedTheory.bounded_division_reconstruct
        >> simp [])
  >> `1099511627776 * r < 18446744073709551616` by
       intLib.ARITH_TAC
  >> `1099511627776 * n =
        q * 18446744073709551616 + 1099511627776 * r` by
       intLib.ARITH_TAC
  >> `(1099511627776 * n) MOD 18446744073709551616 =
        1099511627776 * r` by
       (qpat_x_assum `1099511627776 * n = _`
          (fn th => once_rewrite_tac [th])
        >> irule MOD_UNIQUE
        >> qexists_tac `q`
        >> simp [])
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed64_scale40_128_value:
  bounded_signed128_to_int (bounded_signed64_scale40_128 value) =
    (&1099511627776:int) * bounded_signed64_to_int value
Proof
  Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> Cases_on `magnitude`
  >> simp [bounded_signed64_scale40_128_def,
           compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
           compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
           compute_boundedTheory.bounded128_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           w2n_lsr, word_lsl_n2w, dimword_64]
  >> fs [dimword_64]
  >> assume_tac (Q.INST [`n` |-> `n`] bounded_scale40_num_identity)
  >> fs []
  >> PURE_REWRITE_TAC [GSYM integerTheory.INT_OF_NUM_MUL]
  >> INT_RING_TAC
QED

Theorem bounded128_low40_nonzero_correct:
  bounded128_low40_nonzero magnitude <=>
  bounded128_to_num magnitude MOD 1099511627776 <> 0
Proof
  Cases_on `magnitude`
  >> simp [bounded128_low40_nonzero_def,
           compute_boundedTheory.bounded128_to_num_def,
           compute_boundedTheory.bounded_word_base_eq,
           arithmeticTheory.ADD_MOD, arithmeticTheory.MOD_TIMES,
           compute_boundedSignedTheory.bounded_word64_low40_nonzero_correct]
QED

Theorem bounded_signed128_shift_floor40_64_value:
  bounded_signed128_shift_floor40_64
      (BoundedSigned128 negative magnitude) = SOME result ==>
  bounded_signed64_to_int result =
    if negative then
      -&(bounded128_to_num magnitude DIV 1099511627776 +
         if bounded128_to_num magnitude MOD 1099511627776 = 0
         then 0 else 1)
    else &(bounded128_to_num magnitude DIV 1099511627776)
Proof
  rw [bounded_signed128_shift_floor40_64_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def,
          bounded128_low40_nonzero_correct,
          compute_boundedTheory.bounded128_add_words_refines]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_some
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> fs [compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
         compute_boundedTheory.bounded128_shift_floor40_words_correct,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded_word_base_eq]
QED

Theorem bounded_signed128_shift_ceil40_64_value:
  bounded_signed128_shift_ceil40_64
      (BoundedSigned128 negative magnitude) = SOME result ==>
  bounded_signed64_to_int result =
    if negative then
      -&(bounded128_to_num magnitude DIV 1099511627776)
    else
      &(bounded128_to_num magnitude DIV 1099511627776 +
         if bounded128_to_num magnitude MOD 1099511627776 = 0
         then 0 else 1)
Proof
  rw [bounded_signed128_shift_ceil40_64_def, LET_THM]
  >> every_case_tac
  >> gvs [compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def,
          bounded128_low40_nonzero_correct,
          compute_boundedTheory.bounded128_add_words_refines]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_some
  >> imp_res_tac compute_boundedTheory.bounded128_add_some
  >> fs [compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value,
         compute_boundedTheory.bounded128_shift_floor40_words_correct,
         compute_boundedTheory.bounded128_to_num_def,
         compute_boundedTheory.bounded_word_base_eq]
QED

Theorem bounded_div_ceil40_scaled_ge:
  value <=
    (value DIV 1099511627776 +
       if value MOD 1099511627776 = 0 then 0 else 1) *
      1099511627776
Proof
  mp_tac (Q.SPEC `1099511627776` arithmeticTheory.DIVISION)
  >> simp []
  >> disch_then (qspec_then `value` strip_assume_tac)
  >> Cases_on `value MOD 1099511627776 = 0`
  >> fs [arithmeticTheory.LEFT_ADD_DISTRIB]
  >> qpat_x_assum `value = _` (fn th => once_rewrite_tac [th])
  >> intLib.ARITH_TAC
QED

Theorem bounded_signed128_shift_floor40_64_lower_bound:
  bounded_signed128_shift_floor40_64 source = SOME result ==>
  (&1099511627776:int) * bounded_signed64_to_int result <=
    bounded_signed128_to_int source
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned128 negative magnitude`
  >> strip_tac
  >> imp_res_tac bounded_signed128_shift_floor40_64_value
  >> assume_tac
       (Q.INST [`value` |-> `bounded128_to_num magnitude`]
          compute_boundedIntervalTheory.bounded_div_floor40_scaled_le)
  >> assume_tac
       (Q.INST [`value` |-> `bounded128_to_num magnitude`]
          bounded_div_ceil40_scaled_ge)
  >> Cases_on `negative`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed128_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_signed128_shift_ceil40_64_upper_bound:
  bounded_signed128_shift_ceil40_64 source = SOME result ==>
  bounded_signed128_to_int source <=
    (&1099511627776:int) * bounded_signed64_to_int result
Proof
  Cases_on `source`
  >> rename1 `BoundedSigned128 negative magnitude`
  >> strip_tac
  >> imp_res_tac bounded_signed128_shift_ceil40_64_value
  >> assume_tac
       (Q.INST [`value` |-> `bounded128_to_num magnitude`]
          compute_boundedIntervalTheory.bounded_div_floor40_scaled_le)
  >> assume_tac
       (Q.INST [`value` |-> `bounded128_to_num magnitude`]
          bounded_div_ceil40_scaled_ge)
  >> Cases_on `negative`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed128_to_int_def]
  >> simp [integerTheory.INT_MUL_CALCULATE]
QED

Theorem bounded_taylor_gradient_row_complete_bounds:
  bounded_taylor_gradient_row_complete radii
      (BoundedInterval64 center_lower center_upper) hessian_row =
    SOME (BoundedInterval64 result_lower result_upper) ==>
  ?variation.
    bounded_dot_abs_upper radii hessian_row = SOME variation /\
    (&1099511627776:int) * bounded_signed64_to_int result_lower <=
      (&1099511627776:int) * bounded_signed64_to_int center_lower -
        &(bounded128_to_num variation) /\
    (&1099511627776:int) * bounded_signed64_to_int center_upper +
        &(bounded128_to_num variation) <=
      (&1099511627776:int) * bounded_signed64_to_int result_upper
Proof
  rw [bounded_taylor_gradient_row_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedSignedEndpointAddTheory.bounded_signed128_add_value
  >> imp_res_tac bounded_signed128_shift_floor40_64_lower_bound
  >> imp_res_tac bounded_signed128_shift_ceil40_64_upper_bound
  >> fs [bounded_signed64_scale40_128_value,
         compute_boundedSignedEndpointAddTheory.bounded_signed128_make_value]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
