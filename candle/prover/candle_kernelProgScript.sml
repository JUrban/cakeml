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
  compute_registeredCase10173Tag10GenuineFastChain
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
val r = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_signed_terms_def;
val r = translate
  compute_boundedDeltaTaylorTheory.bounded_delta64_apply_signed_terms_def;
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

(* Exact bounded registration for genuine cells [2048,2064).  The associated
   compute_fast_eval_ok theorem was proved once by the HOL4 evaluator; this
   runtime branch therefore constructs the ordinary Candle equality without
   replaying the generic evaluator. *)
val r = translate
  compute_registeredCase10173HistoricalChunkAt2048Count16DataTheory.registered_case10173_historical_chunk_at2048_count16_ceqs_def;
val r = translate
  compute_registeredCase10173HistoricalChunkAt2048Count16DataTheory.registered_case10173_historical_chunk_at2048_count16_cexp_def;
val r = translate
  compute_registeredCase10173HistoricalChunkAt2048Count16DataTheory.registered_case10173_historical_chunk_at2048_count16_result_def;
val r = translate
  compute_registeredCase10173HistoricalChunkAt2048Count16FastTheory.registered_case10173_historical_chunk_at2048_count16_fast_eval_def;

val r = translate compute_fastChainTheory.compute_fast_eval_chain_def;
val r = translate
  compute_packetFastChainTheory.compute_case10173_packet_fast_eval_def;

(* Decimal interval endpoints and certificate primitives. *)
val _ = translate
  compute_boundedTheory.bounded_word64_mul_div_floor_decimal_def;
val _ = translate
  compute_boundedTheory.bounded_word64_mul_div_ceil_decimal_def;
val _ = translate
  compute_boundedSignedTheory.bounded_signed_word64_mul_floor_decimal_def;
val _ = translate
  compute_boundedSignedTheory.bounded_signed_word64_mul_ceil_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_product_mixed_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def;
val _ = translate
  compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def;

val _ = translate
  compute_boundedCertificateDecimalTheory.bounded_decimal_scale_squared128_def;
val _ = translate
  compute_boundedCertificateDecimalTheory.bounded_interval64_sqrt_certificate_decimal_def;
val _ = translate
  compute_boundedCertificateDecimalTheory.bounded_interval64_inv_certificate_decimal_def;

(* Fused decimal product and compact-Taylor product rule. *)
val _ = translate
  (compute_boundedTheory.bounded192_to_num_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedTaylorFusedDecimalTheory.bounded192_floor64_decimal_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedTaylorFusedDecimalTheory.bounded192_ceil64_decimal_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedTaylorFusedDecimalTheory.bounded_signed192_floor64_decimal_def;
val _ = translate
  compute_boundedTaylorFusedDecimalTheory.bounded_signed192_ceil64_decimal_def;
val _ = translate
  compute_boundedTaylorFusedDecimalTheory.bounded_interval64_fused_products_decimal_def;

val _ = translate
  compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def;
val _ = translate
  compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_scale_add_decimal_def;
val _ = translate
  compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def;
val _ = translate
  compute_boundedTaylorProductDecimalTheory.bounded_interval64_symmetric_outer_decimal_def;

(* Complete decimal Taylor state and multiplication. *)
val _ = translate
  (compute_boundedTheory.bounded128_to_num_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedTaylorCompleteDecimalTheory.bounded128_floor64_decimal_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedTaylorCompleteDecimalTheory.bounded128_ceil64_decimal_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_signed128_floor64_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_signed128_ceil64_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_signed64_scale_decimal128_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_row_complete_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_rows_complete_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_gradient_complete_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_error_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_signed64_scale_two_decimal_squared192_def;
val _ = translate
  (compute_boundedTaylorCompleteDecimalTheory.bounded192_floor64_two_decimal_squared_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedTaylorCompleteDecimalTheory.bounded192_ceil64_two_decimal_squared_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_signed192_floor64_two_decimal_squared_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_signed192_ceil64_two_decimal_squared_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_taylor_value_complete_decimal_def;
val _ = translate
  compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_def;
val _ = translate
  compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_row_def;
val _ = translate
  compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_def;
val _ = translate
  compute_boundedTaylorMulDecimalTheory.bounded_taylor64_mul_decimal_def;

(* Certificate-checked unary functions. *)
val _ = translate
  compute_boundedTaylorUnaryDecimalTheory.bounded_interval64_self_outer_decimal_def;
val _ = translate
  compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_def;
val _ = translate
  compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_inv_certificate_decimal_def;
val _ = translate
  compute_boundedObjectCertificateDecimalTheory.bounded_interval64_positive_sqrt_certificate_decimal_def;
val _ = translate
  compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_inverse_decimal_def;
val _ = translate
  compute_boundedTaylorSqrtDecimalTheory.bounded_taylor64_sqrt_decimal_def;

val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_scale_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_pi_half_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_pos_third_decimal_def;

(* This immutable value is definitionally computed through a pure helper.
   Translate its closed constructor form so the translator can certify that
   its top-level evaluation allocates no references. *)
val bounded_atan_neg_third_decimal_closed =
  EVAL
    ``compute_boundedAtanDecimal$bounded_atan_neg_third_decimal``;
val _ = translate
  bounded_atan_neg_third_decimal_closed;
val _ = DB.fetch
  "candle_kernelProg" "bounded_atan_neg_third_decimal_refs_def";
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_pos_fifth_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_neg_seventh_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_pos_ninth_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_neg_eleventh_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_atan_pos_thirteenth_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_mul_add_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_pos_lower_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_pos_upper_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_unit_lower_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_unit_upper_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_unit_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_range_point_decimal_def;
val _ = translate
  compute_boundedAtanDecimalTheory.bounded_interval64_atan_range_decimal_def;
val _ = translate
  compute_boundedTaylorAtanDecimalTheory.bounded_taylor64_atan_decimal_def;

(* Historical delta at decimal scale. *)
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_source_interval64_sum_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_six_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_source_delta64_value_decimal_def;
val _ = translate
  (compute_boundedHistoricalDeltaDecimalTheory.bounded192_floor64_decimal_squared_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedHistoricalDeltaDecimalTheory.bounded192_ceil64_decimal_squared_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_signed192_floor64_decimal_squared_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_signed192_ceil64_decimal_squared_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_raw_round_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_six_decimal_def;
val _ = translate
  compute_boundedHistoricalDeltaDecimalTheory.bounded_historical_delta64_value_decimal_def;

(* Historical center and box dihedral jets. *)
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_interval64_list_pairwise_mul_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_delta64_pair_products_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_component_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_components_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_source_delta64_gradient_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u_block_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u_three_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u126_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_u135_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_c_vector_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_pi_half_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_def;

val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_component_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_box_entry_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_gradient_box_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_second_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_x4_value_block_decimal_def;

(* The source definition computes this closed table through checked addition
   and negation.  The equality is proved here; translating the equivalent
   constructor table makes the allocation effect syntactically explicit. *)
val bounded_historical_delta_x4_hessian_decimal_closed =
  prove
    (``bounded_historical_delta_x4_hessian_decimal =
        SOME
          [BoundedInterval64
             (BoundedSigned64 T 2000000000000w)
             (BoundedSigned64 T 2000000000000w);
           bounded_atan_one_decimal; bounded_atan_one_decimal;
           BoundedInterval64
             (BoundedSigned64 T 2000000000000w)
             (BoundedSigned64 T 2000000000000w);
           bounded_atan_one_decimal; bounded_atan_one_decimal;
           bounded_interval64_zero;
           BoundedInterval64
             (BoundedSigned64 T 1000000000000w)
             (BoundedSigned64 T 1000000000000w);
           bounded_interval64_zero; bounded_atan_one_decimal;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_atan_one_decimal;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           BoundedInterval64
             (BoundedSigned64 T 1000000000000w)
             (BoundedSigned64 T 1000000000000w);
           bounded_interval64_zero]``,
     EVAL_TAC >> wordsLib.WORD_EVAL_TAC);
val _ = translate
  bounded_historical_delta_x4_hessian_decimal_closed;
val _ = DB.fetch
  "candle_kernelProg"
  "bounded_historical_delta_x4_hessian_decimal_refs_def";
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_x4_second_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_hessian_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_sqrt_second_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_b_hessian_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_entry_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_decimal_def;
val _ = translate
  compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_def;

(* Complete decimal case-10173 cell. *)
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_interval64_unit_vector_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_taylor64_variable_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_source_constant_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_angle_coefficient_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_deferred_scale_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_u_guards_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_add_coordinate_sqrts_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_complete_deferred_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_def;

(* Packed certificate parser and numerical packet checker. *)
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_aux_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_interval64_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_list_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_prefix_def;
val _ = translate
  compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_interval64_list_def;
val _ = translate
  compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_case10173_sqrt64_certificate_def;
val _ = translate
  compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_case10173_sqrt64_certificate_list_def;
val _ = translate
  compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_case10173_packet_def;

Theorem bounded_packed_chars_case10173_decimal_packet_side_total[local]:
  !bytes. bounded_packed_chars_case10173_packet_side bytes
Proof
  rw [fetch "-" "bounded_packed_chars_case10173_packet_side_def"]
  >> imp_res_tac
       compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_interval64_list_two_shape
  >> gvs []
QED

val _ = bounded_packed_chars_case10173_decimal_packet_side_total
  |> update_precondition;

val _ = translate
  compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def;
val _ = translate
  compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packets_def;
val _ = translate
  compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_case10173_full_header_def;
val _ = translate
  compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_full_check_def;

(* Source-shaped calculation used by the strengthened authenticator. *)
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term0_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term1_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term23_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term4_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_term56_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_negative_one_decimal_def;
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_variable_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_def;

(* Likewise, retain the proved source value while registering the seven
   already-checked immutable Taylor constants as constructor data. *)
val bounded_case10173_literal_constants_decimal_closed =
  prove
    (``bounded_case10173_literal_constants_decimal =
        let zeros6 =
          [bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero] in
        let zeros21 =
          [bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero; bounded_interval64_zero;
           bounded_interval64_zero] in
        SOME
          [BoundedTaylor64 T bounded_case10173_literal_term0_decimal
             zeros6 bounded_case10173_literal_term0_decimal zeros6 zeros21;
           BoundedTaylor64 T bounded_case10173_literal_term1_decimal
             zeros6 bounded_case10173_literal_term1_decimal zeros6 zeros21;
           BoundedTaylor64 T bounded_case10173_literal_term23_decimal
             zeros6 bounded_case10173_literal_term23_decimal zeros6 zeros21;
           BoundedTaylor64 T bounded_case10173_literal_term23_decimal
             zeros6 bounded_case10173_literal_term23_decimal zeros6 zeros21;
           BoundedTaylor64 T bounded_case10173_literal_term4_decimal
             zeros6 bounded_case10173_literal_term4_decimal zeros6 zeros21;
           BoundedTaylor64 T bounded_case10173_literal_term56_decimal
             zeros6 bounded_case10173_literal_term56_decimal zeros6 zeros21;
           BoundedTaylor64 T bounded_case10173_literal_term56_decimal
             zeros6 bounded_case10173_literal_term56_decimal zeros6 zeros21]``,
     EVAL_TAC >> wordsLib.WORD_EVAL_TAC);
val _ = translate
  bounded_case10173_literal_constants_decimal_closed;
val _ = DB.fetch
  "candle_kernelProg"
  "bounded_case10173_literal_constants_decimal_refs_def";
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_summands_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_add_stack_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_historical_item_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_source_decimal_def;
val _ = translate
  compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_source_accepts_decimal_def;

(* Source rational decoding and exact source-box coverage. *)
val _ = translate
  compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def;
val _ = translate
  (compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate
  (compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

val _ = translate_no_ind
  (compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_q_interval_list_ind_translation[local]:
  bounded_object_q_interval_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_q_interval_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_q_interval_list_ind_translation
  |> update_precondition;

(* This mathematical view of a signed endpoint is not needed by the
 * numerical-checker lineage itself, but the authenticated source-coverage
 * predicate executes it. *)
val _ = translate
  compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def;

val _ = translate
  compute_boundedObjectDecimalQTheory.bounded_interval64_covers_object_q_ints_decimal_def;
val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedExecutableTheory.bounded_interval64_list_covers_q_pairs_decimal_def;
val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedExecutableTheory.bounded_interval64_list_covers_object_q_decimal_executable_def;

(* Exact decoding of the authenticated historical root records. *)
val _ = translate
  (compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_signed64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate_no_ind
  (compute_boundedObjectDecimalDecodeTheory.bounded_object_decimal_interval64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_decimal_interval64_list_ind_translation[local]:
  bounded_object_decimal_interval64_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_decimal_interval64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_decimal_interval64_list_ind_translation
  |> update_precondition;

(* Canonical decimal conversion of source boxes and source sqrt records. *)
val _ = translate
  (compute_boundedObjectDecimalQTheory.bounded_decimal_natural_floor64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  (compute_boundedObjectDecimalQTheory.bounded_decimal_natural_ceil64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate
  compute_boundedObjectDecimalQTheory.bounded_object_positive_q_floor64_decimal_def;

Theorem bounded_object_positive_q_floor64_decimal_side_total[local]:
  !encoded. bounded_object_positive_q_floor64_decimal_side encoded
Proof
  rw [fetch "-" "bounded_object_positive_q_floor64_decimal_side_def",
      fetch "-" "bounded_decimal_natural_floor64_side_def"]
QED

val _ = bounded_object_positive_q_floor64_decimal_side_total
  |> update_precondition;

val _ = translate
  compute_boundedObjectDecimalQTheory.bounded_object_positive_q_ceil64_decimal_def;

Theorem bounded_object_positive_q_ceil64_decimal_side_total[local]:
  !encoded. bounded_object_positive_q_ceil64_decimal_side encoded
Proof
  rw [fetch "-" "bounded_object_positive_q_ceil64_decimal_side_def",
      fetch "-" "bounded_decimal_natural_ceil64_side_def"]
QED

val _ = bounded_object_positive_q_ceil64_decimal_side_total
  |> update_precondition;

val _ = translate
  (compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate_no_ind
  (compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_object_positive_q_interval64_decimal_list_ind_translation[local]:
  bounded_object_positive_q_interval64_decimal_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_object_positive_q_interval64_decimal_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_object_positive_q_interval64_decimal_list_ind_translation
  |> update_precondition;

(* Packet/source identity relations. *)
val _ = translate
  compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def;
val _ = translate
  compute_boundedCase10173JobBindingTheory.bounded_case10173_object_job_boxes_def;
val _ = translate
  compute_boundedCase10173HistoricalCellDecimalBoundaryTheory.bounded_case10173_decimal_packet_box_binds_object_job_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_center_intervals_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_box_intervals_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_def;
val _ = translate
  compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def;
val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedExecutableTheory.bounded_interval64_list_prefix_one_extra_def;
val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedExecutableTheory.bounded_case10173_decimal_packet_sqrt_roots_bind_object_job_executable_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_roots_bind_object_record_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_box_exact_object_job_def;
val _ = translate
  compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def;
val _ = translate
  compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_midpoint_positive_cv_def;
val _ = translate
  compute_registeredCase10173CenterEnvironmentObjectTheory.registered_case10173_q_center_environment_positive_def;
val _ = translate
  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def;
val _ = translate
  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_center_exact_object_job_def;
val _ = translate
  compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def;

(* Exact source-rational square-root certificates. *)
val _ = translate
  compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_certificate_exact_def;
val _ = translate
  compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_q_sqrt_prefix_exact_def;
val _ = translate
  compute_boundedCase10173SourceSqrtCertificateTheory.bounded_case10173_source_coordinate_sqrts_exact_def;

(* Exact identity of source roots and typed decimal roots. *)
val _ = translate
  compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_positive_endpoint64_q_cv_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_endpoint64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_positive_q_interval64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_decimal_prefix_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_coordinate_sqrt_decimals_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_floor64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_ceil64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_interval64_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_sqrt_dd_prefix_exact_def;
val _ = translate
  compute_boundedCase10173SourceDecimalExactTheory.bounded_case10173_source_coordinate_sqrt_dd_decimals_exact_def;

(* Exact source-radius reconstruction from the authenticated rational box. *)
val _ = translate
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_packet_radii_def;
val _ = translate
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radius64_positive_q_def;

Theorem bounded_case10173_source_radius64_positive_q_side_total[local]:
  !encoded. bounded_case10173_source_radius64_positive_q_side encoded
Proof
  rw [fetch "-" "bounded_case10173_source_radius64_positive_q_side_def",
      fetch "-" "bounded_decimal_natural_ceil64_side_def"]
QED

val _ = bounded_case10173_source_radius64_positive_q_side_total
  |> update_precondition;

val _ = translate_no_ind
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_source_radii64_positive_q_def;

Theorem bounded_case10173_source_radii64_positive_q_ind_translation[local]:
  bounded_case10173_source_radii64_positive_q_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_case10173_source_radii64_positive_q_ind_def"]
  >> gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

val _ = bounded_case10173_source_radii64_positive_q_ind_translation
  |> update_precondition;

val _ = translate
  compute_registeredCase10173RadiusBindingTheory.bounded_case10173_decimal_packet_source_radii_exact_def;

(* Authenticate the actual completed operands supplied to source sqrt. *)
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_positive_interval64_q_cv_def;
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def;
val _ = translate
  compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_source_actual_sqrt_contract_def;

val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_packets_def;
val _ = translate
  compute_boundedCase10173PackedDecimalAuthenticatedTheory.bounded_packed_chars_case10173_decimal_authenticated_full_check_def;

(* Exact registered source identity and approved equation environment. *)
val _ = translate_closed
  compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_source_program_def;
val _ = translate
  compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_ceqs_def;
val _ = translate
  compute_registeredCase10173HistoricalChunk16Tag10DataTheory.registered_case10173_historical_chunk16_tag10_ceqs_def;

(* Generic three-payload fast-dispatch seam. *)
val _ = translate
  compute_payload3FastTheory.compute_literal_call_payload3_def;
val _ = translate
  compute_payload3FastTheory.compute_payload3_call_fast_eval_def;

(* Authenticated case-10173 dispatcher closed over the approved program. *)
val _ = translate
  compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_checker_def;
val _ = translate
  compute_registeredCase10173AuthenticatedFastDispatchTheory.registered_case10173_decimal_authenticated_fast_eval_def;

(* Corrected authenticated dispatcher.  The old dispatcher remains translated
   only for the existing fallback surface; the production full-stream branch
   below is closed over the exact tag-10 equation environment. *)
val _ = translate
  compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_checker_def;
val _ = translate
  compute_registeredCase10173Tag10AuthenticatedFastDispatchTheory.registered_case10173_tag10_decimal_authenticated_fast_eval_def;

(* Add the immutable 4,707,156-byte payload as one proved CakeML literal.
   Keeping the HOL value behind an abbreviation prevents every subsequent
   translator theorem from copying the complete literal syntax tree. *)
val registered_case10173_genuine_packed_certificate_payload =
  compute_registeredCase10173GenuineCertificateDataTheory.registered_case10173_genuine_packed_certificate_def
  |> concl |> rhs;

val registered_case10173_genuine_packed_certificate_term =
  compute_registeredCase10173GenuineCertificateDataTheory.registered_case10173_genuine_packed_certificate_def
  |> concl |> lhs;

val registered_case10173_genuine_packed_certificate_value_def =
  ml_progLib.define_abbrev false
    "registered_case10173_genuine_packed_certificate_value"
    (semanticPrimitivesSyntax.mk_Litv
      (astSyntax.mk_StrLit
        registered_case10173_genuine_packed_certificate_term));

val registered_case10173_genuine_packed_certificate_literal_value_def =
  registered_case10173_genuine_packed_certificate_value_def
  |> PURE_REWRITE_RULE
       [compute_registeredCase10173GenuineCertificateDataTheory.registered_case10173_genuine_packed_certificate_def];

val registered_case10173_genuine_packed_certificate_value =
  registered_case10173_genuine_packed_certificate_value_def
  |> concl |> lhs;

val _ =
  ml_prog_update
    (ml_progLib.add_Dlet_lit_abbrev
      (locationTheory.unknown_loc_def |> concl |> dest_eq |> fst)
      (mlstringSyntax.mk_mlstring
        "registered_case10173_genuine_packed_certificate")
      (astSyntax.mk_StrLit
        registered_case10173_genuine_packed_certificate_payload)
      registered_case10173_genuine_packed_certificate_literal_value_def);

val registered_case10173_genuine_packed_certificate_env_lookup =
  ml_progLib.get_env (ml_translatorLib.get_ml_prog_state ())
  |> strip_comb |> snd |> hd
  |> dest_thy_const |> #Name
  |> (fn env_name => fetch "-" ("nsLookup_" ^ env_name ^ "_pfun_eqs"));

Theorem registered_case10173_genuine_packed_certificate_value_relation:
  STRING_TYPE
    registered_case10173_genuine_packed_certificate
    ^registered_case10173_genuine_packed_certificate_value
Proof
  simp [ml_translatorTheory.STRING_TYPE_def,
        registered_case10173_genuine_packed_certificate_value_def]
QED

Theorem registered_case10173_genuine_packed_certificate_v_thm:
  Eval ^(ml_progLib.get_env (ml_translatorLib.get_ml_prog_state ()))
    (Var (Short «registered_case10173_genuine_packed_certificate»))
    (STRING_TYPE registered_case10173_genuine_packed_certificate)
Proof
  simp [ml_translatorTheory.Eval_Var,
        ml_progTheory.lookup_var_def,
        ml_progTheory.nsLookup_merge_env,
        ml_progTheory.option_choice_f_apply,
        GSYM ml_progTheory.nsLookup_Short_def,
        registered_case10173_genuine_packed_certificate_env_lookup,
        registered_case10173_genuine_packed_certificate_value_relation]
QED

val _ =
  ml_translatorLib.add_v_thms
    ("registered_case10173_genuine_packed_certificate",
     "registered_case10173_genuine_packed_certificate",
     registered_case10173_genuine_packed_certificate_v_thm,
     TRUTH);

(* Close the genuine evaluator over the authenticated literal and compose it
   ahead of the existing packet/general evaluator chain. *)
val _ = translate
  compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_packed_certificate_bytes_def;
val _ = translate
  compute_registeredCase10173Tag10GenuineAuthenticatedFastTheory.registered_case10173_tag10_genuine_decimal_authenticated_fast_eval_def;
val _ = translate
  compute_registeredCase10173Tag10GenuineFastChainTheory.compute_case10173_tag10_genuine_fast_eval_def;

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["compute"];
val r = compute_case10173_tag10_genuine_fast_def
        |> SIMP_RULE(srw_ss()) [compute_with_def, combinTheory.C_DEF]
        |> check [‘ths’,‘ceqs’,‘tm’]
        |> m_translate;

(* Preserve the semantic name consumed by the existing kernel interface. *)
Definition compute_v_alias_def:
  compute_v = compute_case10173_tag10_genuine_fast_v
End

Theorem compute_v_def =
  fetch "-" "compute_case10173_tag10_genuine_fast_v_def"
  |> REWRITE_RULE [GSYM compute_v_alias_def];

Theorem compute_v_thm =
  fetch "-" "compute_case10173_tag10_genuine_fast_v_thm"
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
