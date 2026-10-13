(*
  Adds Candle specific functions to the kernel module from ml_hol_kernel_funsProg
*)
Theory candle_kernelProg
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib
  basisFunctionsLib runtime_checkLib
Ancestors
  ml_hol_kernel_funsProg compute print_thm
  (* compute: *) compute_syntax compute_eval compute_pmatch
  compute_pureFast
  compute_packetFastChain
  compute_boundedCase10173Packet
  runtime_check

val _ = m_translation_extends "ml_hol_kernel_funsProg"

val _ = (use_long_names := false);

val _ = ml_prog_update open_local_block;

val r = translate ty_to_v_def;
val r = translate term_to_v_def;
val r = translate thm_to_v_def;
val r = translate update_to_v_def;
val r = translate thm_to_string_def;

val _ = ml_prog_update open_local_in_block;

Quote add_cakeml:
  val print_thm = fn th => case th of Sequent tms c =>
    let
      val ctxt = !the_context
      val str = thm_to_string ctxt th
      val arr = Word8Array.array 0 (Word8.fromInt 0)
    in
      #(kernel_ffi) str arr
    end;
End
(* compute primitive *)

val _ = ml_prog_update open_local_block;

val r = translate dest_num_PMATCH;
val r = m_translate dest_numeral_PMATCH;
val r = translate dest_numeral_opt_PMATCH;
val r = translate list_dest_comb_def;
val r = translate mapOption_def;
val r = translate app_type_def;
val r = translate dest_cexp_def;

Theorem dest_cexp_side[local]:
  ∀x. dest_cexp_side x
Proof
  ho_match_mp_tac dest_cexp_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "dest_cexp_side_def"] \\ rw []
QED

val _ = update_precondition dest_cexp_side;

val r = m_translate option_def;
val r = m_translate check_def;
val r = translate SAFEMOD_def;
val r = translate SAFEDIV_def;
val r = translate num2bit_def;
val r = translate compute_execTheory.cv2term_def

val r = compute_thms_def |> EVAL_RULE |> translate;

val r = m_translate dest_binary_PMATCH;

val r = check [‘ths’] compute_init_def |> translate;

val r = m_translate check_var_def;

val _ = use_mem_intro := true;
val res = translate_no_ind check_cexp_closed_def;

Theorem check_cexp_closed_ind[local]:
  check_cexp_closed_ind
Proof
  rewrite_tac [fetch "-" "check_cexp_closed_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD, GSYM ml_translatorTheory.MEMBER_INTRO]
QED

val _ = check_cexp_closed_ind |> update_precondition;
val _ = use_mem_intro := false;

val r = translate var_list_def;

val r = translate const_list_def;
val r = m_translate map_def;

val _ = use_mem_intro := true;
val r = m_translate check_consts_def;
val r = m_translate check_eqn_def;
val _ = use_mem_intro := false;

val r = translate compute_default_clock; (* TODO _def *)
val r = translate indexedListsTheory.findi_def
val r = translate compute_execTheory.monop_fst_def
val r = translate compute_execTheory.monop_snd_def
val r = translate compute_execTheory.monop_ispair_def
val r = translate compute_execTheory.monop_def
val r = translate compute_execTheory.to_num_def
val r = translate compute_execTheory.cv_T_def
val r = translate compute_execTheory.cv_F_def
val r = translate compute_execTheory.binop_add_def
val r = translate (compute_execTheory.binop_sub_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val r = translate compute_execTheory.binop_mul_def
val r = translate compute_execTheory.binop_div_def
val r = translate compute_execTheory.binop_mod_def
val r = translate compute_execTheory.binop_eq_def
val r = translate compute_execTheory.binop_less_def
val r = translate compute_execTheory.binop_def
val r = translate compute_execTheory.to_ce_def
val r = translate compute_execTheory.compile_to_ce_def
val r = translate compute_execTheory.build_funs_def
val r = translate compute_execTheory.env_lookup_def

val r = m_translate compute_execTheory.get_code_def
val r = m_translate compute_execTheory.exec_def

val _ = ml_prog_update open_local_in_block;

val r = check [‘ths’,‘tm’] compute_add_def |> m_translate;

(* The fast evaluator and its numerical tables are implementation details of
 * the privileged [compute] entry point.  Keep them in a nested local block:
 * exporting their closures would also export the captured kernel-reference
 * environment, whereas [compute_v] is already covered by the kernel-function
 * invariant and its dedicated refinement theorem. *)
val _ = ml_prog_update open_local_block;

(*
 * General proof-producing fast path.  This is the same first-order source
 * evaluator used by the offline refinement proof, now translated as ordinary
 * CakeML and installed behind compute_with.  A successful result is accepted
 * by the kernel using compute_pure_fast_eval_ok; fuel exhaustion or any
 * malformed input falls back to the existing verified exec evaluator.
 *)
val r = translate compute_evalPureTheory.compute_pure_to_num_def;
val r = translate compute_evalPureTheory.compute_pure_uop_def;
val r = translate
  (compute_evalPureTheory.compute_pure_binop_def
   |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val r = translate compute_evalPureTheory.compute_pure_remove_binding_def;
val r = translate compute_evalPureTheory.compute_pure_subst_def;
val r = translate compute_evalPureTheory.compute_eval_pure_def;
val r = translate compute_pureFastTheory.compute_exp_to_cv_def;
val r = translate compute_pureFastTheory.compute_pure_fast_fuel_def;
val r = translate compute_pureFastTheory.compute_pure_fast_eval_def;

(* Proved fixed-width substrate for the specialized nonlinear packet path.
   This must be installed before Kernel is closed: packet decoding consumes
   this module's existing cv constructors and may not recreate their stamps
   in a later translator state. *)
val _ = register_type ``:bounded128``;
val _ = register_type ``:bounded192``;

val r = translate compute_boundedTheory.bounded_word64_add_carry_def;
val r = translate compute_boundedTheory.bounded_word64_mul_full_chunks22_def;
val r = translate compute_boundedTheory.bounded_word64_mul_shift_floor40_def;
val r = translate compute_boundedTheory.bounded128_shift_floor40_words_def;
val r = translate compute_boundedTheory.bounded128_add_words_def;
val r = translate compute_boundedTheory.bounded192_add_words_def;

val _ = register_type ``:bounded_signed64``;
val _ = register_type ``:bounded_signed128``;

val r = translate compute_boundedSignedTheory.bounded128_is_zero_def;
val r = translate compute_boundedSignedTheory.bounded_signed128_make_def;
val r = translate compute_boundedSignedTheory.bounded_signed128_negative_def;
val r = translate compute_boundedSignedTheory.bounded_signed128_magnitude_def;
val r = translate compute_boundedSignedTheory.bounded_word64_low40_nonzero_def;
val r = translate compute_boundedSignedTheory.bounded_word64_mul_shift_ceil40_def;
val r = translate compute_boundedSignedTheory.bounded_signed_word64_mul_floor40_def;
val r = translate compute_boundedSignedTheory.bounded_signed_word64_mul_ceil40_def;
val r = translate compute_boundedSignedAddTheory.bounded128_le_words_def;
val r = translate compute_boundedSignedAddTheory.bounded_word64_sub_borrow_def;
val r = translate compute_boundedSignedAddTheory.bounded128_sub_words_def;
val r = translate compute_boundedSignedAddTheory.bounded_signed128_add_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_make_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_widen128_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed128_narrow64_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_le_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_min_def;
val r = translate compute_boundedSignedEndpointTheory.bounded_signed64_max_def;
val r = translate compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def;
val r = translate compute_boundedSignedEndpointAddTheory.bounded_signed64_add_def;

val _ = register_type ``:bounded_interval64``;

val r = translate compute_boundedIntervalTheory.bounded_interval64_lower_def;
val r = translate compute_boundedIntervalTheory.bounded_interval64_upper_def;
val r = translate compute_boundedIntervalTheory.bounded_signed64_nonnegative_def;
val r = translate compute_boundedIntervalTheory.bounded_signed64_nonpositive_def;
val r = translate compute_boundedIntervalTheory.bounded_scaled_mul_floor64_def;
val r = translate compute_boundedIntervalTheory.bounded_scaled_mul_ceil64_def;
val r = translate compute_boundedIntervalTheory.bounded_interval64_product_from_pairs_def;
val r = translate compute_boundedIntervalTheory.bounded_interval64_product_mixed_def;
val r = translate compute_boundedIntervalTheory.bounded_interval64_mul_unchecked_def;
val r = translate compute_boundedIntervalTheory.bounded_interval64_valid_def;
val r = translate compute_boundedIntervalTheory.bounded_interval64_mul_def;
val r = translate compute_boundedIntervalAddTheory.bounded_interval64_neg_def;
val r = translate compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def;
val r = translate compute_boundedIntervalAddTheory.bounded_interval64_add_def;
val r = translate compute_boundedIntervalListTheory.bounded_interval64_zero_def;
val r = translate compute_boundedIntervalListTheory.bounded_interval64_list_valid_def;
val r = translate compute_boundedIntervalListTheory.bounded_interval64_list_neg_def;
val r = translate compute_boundedIntervalListTheory.bounded_interval64_list_add_def;
val r = translate compute_boundedIntervalListTheory.bounded_interval64_list_scale_def;
val r = translate compute_boundedIntervalListTheory.bounded_interval64_list_pairwise_mul_def;
val r = translate compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def;
val r = translate compute_boundedTaylorStateTheory.bounded_taylor64_make_def;
val r = translate compute_boundedTaylorStateTheory.bounded_taylor64_add_unchecked_def;
val r = translate compute_boundedTaylorStateTheory.bounded_taylor64_add_def;
val r = translate compute_boundedWideTheory.bounded192_zero_def;
val r = translate compute_boundedWideTheory.bounded_word64_sub_borrow_in_def;
val r = translate compute_boundedWideTheory.bounded192_le_words_def;
val r = translate compute_boundedWideTheory.bounded192_sub_words_def;
val r = translate compute_boundedWideTheory.bounded128_mul_word64_to_192_words_def;

val _ = register_type ``:bounded_signed192``;

val r = translate compute_boundedWideSignedTheory.bounded192_is_zero_def;
val r = translate compute_boundedWideSignedTheory.bounded_signed192_make_def;
val r = translate compute_boundedWideSignedTheory.bounded_signed192_add_def;
val r = translate compute_boundedWideSignedTheory.bounded_signed64_scale81_def;
val r = translate compute_boundedWideSignedTheory.bounded128_scale41_def;
val r = translate compute_boundedWideSignedTheory.bounded192_shift_floor81_words_def;
val r = translate compute_boundedWideSignedTheory.bounded192_low81_nonzero_def;
val r = translate compute_boundedWideSignedTheory.bounded_signed128_narrow64_option_def;
val r = translate compute_boundedWideSignedTheory.bounded_signed192_shift_floor81_64_def;
val r = translate compute_boundedWideSignedTheory.bounded_signed192_shift_ceil81_64_def;

val r = translate compute_boundedTaylorCompleteTheory.bounded_interval64_abs_upper_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_word64_product128_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_acc_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_dot_abs_upper_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_acc_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_quadratic_abs_upper_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_taylor_error_def;
val r = translate compute_boundedTaylorCompleteTheory.bounded_taylor_value_complete_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_signed64_scale40_128_def;
val r = translate compute_boundedTaylorGradientTheory.bounded128_low40_nonzero_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_signed128_shift_floor40_64_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_signed128_shift_ceil40_64_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_taylor_gradient_row_complete_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_taylor_gradient_rows_complete_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_taylor_gradient_complete_def;
val r = translate compute_boundedTaylorGradientTheory.bounded_taylor64_complete_def;
val r = translate compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_def;
val r = translate compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def;
val r = translate compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def;
val r = translate compute_boundedReciprocalCertificateTheory.bounded_scale_squared128_def;
val r = translate compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def;
val r = translate compute_boundedAtanTheory.bounded_atan_word64_def;

(* Closed immutable data should enter the generated initial state as literal
 * values.  Normalizing its right-hand side before translation also gives the
 * translator a syntactic no-change-of-references proof; leaving the helper
 * calls here would introduce unconstrained reference tails in the state. *)
fun translate_closed def =
  def |> CONV_RULE (RAND_CONV EVAL) |> translate;

val r = translate_closed compute_boundedAtanTheory.bounded_atan_scale_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_one_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_pi_half_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_pos_third_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_neg_third_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_pos_fifth_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_neg_seventh_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_pos_ninth_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_neg_eleventh_def;
val r = translate_closed compute_boundedAtanTheory.bounded_atan_pos_thirteenth_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_mul_add_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_pos_lower_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_pos_upper_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_unit_lower_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_unit_upper_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_unit_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_range_point_def;
val r = translate compute_boundedAtanTheory.bounded_interval64_atan_range_def;

val r = translate compute_boundedTaylorMulTheory.bounded_signed64_raw_product_def;
val r = translate compute_boundedTaylorMulTheory.bounded_signed128_le_words_def;
val r = translate compute_boundedTaylorMulTheory.bounded_signed128_min_def;
val r = translate compute_boundedTaylorMulTheory.bounded_signed128_max_def;
val r = translate compute_boundedTaylorMulTheory.bounded_interval64_raw_product_from_pairs_def;
val r = translate compute_boundedTaylorMulTheory.bounded_interval64_raw_product_mixed_def;
val r = translate compute_boundedTaylorMulTheory.bounded_interval64_raw_mul_bounds_unchecked_def;
val r = translate compute_boundedTaylorMulTheory.bounded_signed128_widen192_def;
val r = translate compute_boundedTaylorMulTheory.bounded_interval64_raw_sum_acc_def;
val r = translate compute_boundedTaylorMulTheory.bounded192_shift_floor40_128_def;
val r = translate compute_boundedTaylorMulTheory.bounded192_low40_nonzero_def;
val r = translate compute_boundedTaylorMulTheory.bounded_signed192_shift_floor40_64_def;
val r = translate compute_boundedTaylorMulTheory.bounded_signed192_shift_ceil40_64_def;
val r = translate compute_boundedTaylorMulTheory.bounded_interval64_fused_products_def;
val r = translate compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def;
val r = translate compute_boundedTaylorBaseTheory.bounded_interval64_nth_def;
val r = translate compute_boundedTaylorBaseTheory.bounded_interval64_unit_vector_def;
val r = translate compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def;
val r = translate compute_boundedTaylorBaseTheory.bounded_taylor64_variable_def;
val r = translate compute_boundedTaylorUnaryTheory.bounded_interval64_self_outer_def;
val r = translate compute_boundedTaylorUnaryTheory.bounded_taylor64_unary_complete_def;
val r = translate compute_boundedTaylorSqrtTheory.bounded_taylor64_sqrt_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_sum_aux_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_sum_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_list_scale4_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_mul3_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_sums_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_pair_products_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_component_from_products_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_value_six_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_value_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_interval64_list_add_at_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_neg_derivative_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_entry_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_product_hessian_def;
val r = translate compute_boundedDeltaTaylorTheory.bounded_delta64_four_coordinate_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_le_words_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_min_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_max_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_neg_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed128_nonnegative_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed128_nonpositive_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed128_mul_signed64_raw192_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_from_pairs_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_product_mixed_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_raw128_interval_mul64_unchecked_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubic_signed_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_historical_raw_cubics_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_aux_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_interval_sum_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded192_shift_floor80_words_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded192_low80_nonzero_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_shift_floor80_64_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_signed192_shift_ceil80_64_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_historical_raw_round80_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_historical_delta64_value_six_def;
val r = translate compute_boundedHistoricalDeltaTheory.bounded_historical_delta64_value_def;

val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_negative_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_upper_positive_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_negative_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_lower_positive_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_block_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u_three_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u126_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_u135_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_value_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_c_vector_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_replace_three_def;
val r = translate compute_boundedHistoricalDihedralFirstTheory.bounded_historical_dihedral_first64_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_extreme_interval_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_coordinate_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_monotone_environment_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_gradient_component_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_gradient_box_entry_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_gradient_box_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_second_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_x4_value_block_def;
val r = translate_closed
  compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_x4_hessian_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_delta_x4_second_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_sqrt_hessian_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_sqrt_second_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_b_hessian_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_second_hessian_entry_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_second_hessian_def;
val r = translate compute_boundedHistoricalDihedralSecondTheory.bounded_historical_dihedral_second64_def;

val _ = register_type ``:bounded_case10173_sqrt64_certificate``;

val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_root_coefficients_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_source_constant_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_angle_coefficient_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_defer_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_scale_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_add_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_radius_covers_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_geometry_ok_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_positive_environment_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_u_guards_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_add_coordinate_sqrts_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_angle_state_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_complete_deferred_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_checked_cell64_def;
val r = translate compute_boundedCase10173HistoricalCellTheory.bounded_case10173_checked_cell_accepts_def;

val _ = register_type ``:bounded_case10173_packet``;

val r = translate bounded_cv_encode_word64_def;
val r = translate
  (bounded_cv_decode_word64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val r = translate bounded_cv_encode_bool_def;
val r = translate bounded_cv_decode_bool_def;
val r = translate bounded_cv_encode_signed64_def;
val r = translate
  (bounded_cv_decode_signed64_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val r = translate bounded_cv_encode_interval64_def;
val r = translate
  (bounded_cv_decode_interval64_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val r = translate bounded_cv_encode_word64_list_def;

Theorem bounded_cv_tail_induction[local]:
  !P. (!v:cv. (!x y. v = Pair x y ==> P y) ==> P v) ==> !v. P v
Proof
  gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

val r = translate_no_ind
  (bounded_cv_decode_word64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_decode_word64_list_ind[local]:
  bounded_cv_decode_word64_list_ind
Proof
  once_rewrite_tac [fetch "-" "bounded_cv_decode_word64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_cv_decode_word64_list_ind |> update_precondition;

val r = translate bounded_cv_encode_interval64_list_def;
val r = translate_no_ind
  (bounded_cv_decode_interval64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_decode_interval64_list_ind[local]:
  bounded_cv_decode_interval64_list_ind
Proof
  once_rewrite_tac [fetch "-" "bounded_cv_decode_interval64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_cv_decode_interval64_list_ind |> update_precondition;

val r = translate bounded_cv_encode_sqrt64_certificate_def;
val r = translate
  (bounded_cv_decode_sqrt64_certificate_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val r = translate bounded_cv_encode_sqrt64_certificate_list_def;
val r = translate_no_ind
  (bounded_cv_decode_sqrt64_certificate_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_decode_sqrt64_certificate_list_ind[local]:
  bounded_cv_decode_sqrt64_certificate_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_cv_decode_sqrt64_certificate_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_cv_decode_sqrt64_certificate_list_ind
  |> update_precondition;

val r = translate bounded_case10173_packet_well_shaped_def;
val r = translate bounded_cv_encode_case10173_packet_def;
val r = translate
  (bounded_cv_decode_case10173_packet_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val r = translate bounded_case10173_packet_accepts_def;
val r = translate bounded_case10173_packet_check_cv_def;

val r = translate
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_positive_interval_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_environment_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_environment_def;
val r = translate
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_radii_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_sqrt_certificates_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_root_delta_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_root_four_x0_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_center_reciprocals_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_root_delta_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_root_four_x0_def;
val r = translate_closed
  compute_boundedCase10173HistoricalCell0DataTheory.bounded_case10173_cell0_box_reciprocals_def;
val r = translate bounded_case10173_cell0_packet_def;

val r = translate
  compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_ceqs_def;
val r = translate
  compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_cexp_def;
val r = translate
  compute_registeredCase10173Cell0DataTheory.registered_case10173_cell0_result_def;
val r = translate
  compute_registeredCase10173PacketFastTheory.registered_case10173_cell0_packet_fast_eval_def;
val r = translate compute_fastChainTheory.compute_fast_eval_chain_def;
val r = translate
  compute_packetFastChainTheory.compute_case10173_packet_fast_eval_def;

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["compute"];
val r = compute_case10173_packet_fast_def
        |> SIMP_RULE(srw_ss()) [compute_with_def, combinTheory.C_DEF]
        |> check [‘ths’,‘ceqs’,‘tm’]
        |> m_translate;

(* Preserve the semantic name consumed by the existing kernel interface. *)
Definition compute_v_alias_def:
  compute_v = compute_case10173_packet_fast_v
End

Theorem compute_v_def =
  fetch "-" "compute_case10173_packet_fast_v_def"
  |> REWRITE_RULE [GSYM compute_v_alias_def];

Theorem compute_v_thm =
  fetch "-" "compute_case10173_packet_fast_v_thm"
  |> REWRITE_RULE [GSYM compute_v_alias_def];

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* extract the interesting theorem *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

Theorem candle_prog_thm =
  get_Decls_thm (get_ml_prog_state())
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"));

(* extract some other other theorems *)

Theorem EqualityType_TYPE_TYPE = EqualityType_rule [] “:type”;

Theorem EqualityType_TERM_TYPE = EqualityType_rule [] “:term”;

Theorem EqualityType_THM_TYPE = EqualityType_rule [] “:thm”;

Theorem EqualityType_UPDATE_TYPE = EqualityType_rule [] “:update”;

val _ = (print_asts := true);
