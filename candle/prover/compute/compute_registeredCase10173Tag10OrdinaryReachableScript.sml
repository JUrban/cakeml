(*****************************************************************************
 * Closed call graph shared by every ordinary case-10173 fixed/nonlinear
 * instruction across the historical and corrected tag-10 environments.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10OrdinaryReachable
Ancestors
  compute_evalRestrictedCongruence
  compute_registeredCase10173HistoricalChunk16Data
  compute_registeredCase10173HistoricalChunk16Tag10Data
  compute_registeredCase10173Tag10EnvironmentDelta
Libs
  bossLib preamble

Definition registered_case10173_tag10_ordinary_reachable_def:
  registered_case10173_tag10_ordinary_reachable : mlstring list =
    [«candle_cv_bool_and»;
     «candle_cv_fs_add»;
     «candle_cv_fs_canonical»;
     «candle_cv_fs_ceil_div»;
     «candle_cv_fs_dot_abs_upper»;
     «candle_cv_fs_first_gradient»;
     «candle_cv_fs_first_make»;
     «candle_cv_fs_first_value»;
     «candle_cv_fs_floor_div»;
     «candle_cv_fs_gradient_bounds»;
     «candle_cv_fs_interval_abs_upper»;
     «candle_cv_fs_interval_add»;
     «candle_cv_fs_interval_constant»;
     «candle_cv_fs_interval_list_add»;
     «candle_cv_fs_interval_list_neg»;
     «candle_cv_fs_interval_list_of_q»;
     «candle_cv_fs_interval_list_to_q»;
     «candle_cv_fs_interval_lookup»;
     «candle_cv_fs_interval_matrix_add»;
     «candle_cv_fs_interval_matrix_neg»;
     «candle_cv_fs_interval_matrix_to_q»;
     «candle_cv_fs_interval_neg»;
     «candle_cv_fs_interval_of_q»;
     «candle_cv_fs_interval_one»;
     «candle_cv_fs_interval_to_q»;
     «candle_cv_fs_interval_unit»;
     «candle_cv_fs_interval_zero»;
     «candle_cv_fs_interval_zero_matrix»;
     «candle_cv_fs_interval_zeros»;
     «candle_cv_fs_list_of_q»;
     «candle_cv_fs_neg»;
     «candle_cv_fs_of_q_lower»;
     «candle_cv_fs_of_q_upper»;
     «candle_cv_fs_one»;
     «candle_cv_fs_poly_program»;
     «candle_cv_fs_poly_program_fixed»;
     «candle_cv_fs_poly_run»;
     «candle_cv_fs_poly_step»;
     «candle_cv_fs_raw_abs»;
     «candle_cv_fs_raw_add»;
     «candle_cv_fs_raw_interval_add»;
     «candle_cv_fs_raw_interval_list_add»;
     «candle_cv_fs_raw_interval_list_round»;
     «candle_cv_fs_raw_interval_list_scale»;
     «candle_cv_fs_raw_interval_matrix_add»;
     «candle_cv_fs_raw_interval_matrix_round»;
     «candle_cv_fs_raw_interval_matrix_scale»;
     «candle_cv_fs_raw_interval_mul»;
     «candle_cv_fs_raw_interval_outer»;
     «candle_cv_fs_raw_interval_round»;
     «candle_cv_fs_raw_le»;
     «candle_cv_fs_raw_max»;
     «candle_cv_fs_raw_min»;
     «candle_cv_fs_raw_mul»;
     «candle_cv_fs_raw_neg»;
     «candle_cv_fs_raw_scale»;
     «candle_cv_fs_result_add»;
     «candle_cv_fs_result_center»;
     «candle_cv_fs_result_complete_raw»;
     «candle_cv_fs_result_complete_rounded»;
     «candle_cv_fs_result_constant»;
     «candle_cv_fs_result_domain»;
     «candle_cv_fs_result_gradient_bounds»;
     «candle_cv_fs_result_head»;
     «candle_cv_fs_result_hessian»;
     «candle_cv_fs_result_make»;
     «candle_cv_fs_result_mul»;
     «candle_cv_fs_result_neg»;
     «candle_cv_fs_result_square»;
     «candle_cv_fs_result_tail»;
     «candle_cv_fs_result_to_q»;
     «candle_cv_fs_result_value_bound»;
     «candle_cv_fs_result_variable»;
     «candle_cv_fs_result_zero»;
     «candle_cv_fs_scale»;
     «candle_cv_fs_scale_squared»;
     «candle_cv_fs_to_q»;
     «candle_cv_fs_two_scale_squared»;
     «candle_cv_fs_weighted_rows_abs_upper»;
     «candle_cv_fs_zero»;
     «candle_cv_fsa_interval_matrix_of_q»;
     «candle_cv_fsa_item_add»;
     «candle_cv_fsa_item_default»;
     «candle_cv_fsa_item_fixed»;
     «candle_cv_fsa_item_head»;
     «candle_cv_fsa_item_is_fixed»;
     «candle_cv_fsa_item_payload»;
     «candle_cv_fsa_item_q»;
     «candle_cv_fsa_item_tail»;
     «candle_cv_fsa_item_to_fixed»;
     «candle_cv_fsa_item_to_q»;
     «candle_cv_fsa_result_of_q»;
     «candle_cv_fsn_first_sqrt»;
     «candle_cv_fsn_interval_list_scale»;
     «candle_cv_fsn_interval_matrix_scale»;
     «candle_cv_fsn_interval_outer»;
     «candle_cv_fsn_item_sqrt»;
     «candle_cv_fsn_result_sqrt»;
     «candle_cv_fsn_sqrt_domain»;
     «candle_cv_fsn_sqrt_hessian»;
     «candle_cv_fso_item_mul»;
     «candle_cv_lc_zadd»;
     «candle_cv_lc_znormalize»;
     «candle_cv_lc_zscale»;
     «candle_cv_num_gcd»;
     «candle_cv_num_gcd_extended»;
     «candle_cv_num_gcd_state_chunk»;
     «candle_cv_num_gcd_state_finish»;
     «candle_cv_num_gcd_state_fuel»;
     «candle_cv_num_gcd_state_resume»;
     «candle_cv_q_abs_upper»;
     «candle_cv_q_add»;
     «candle_cv_q_add_normalized_extended»;
     «candle_cv_q_ceil_div»;
     «candle_cv_q_den»;
     «candle_cv_q_den_product_pred»;
     «candle_cv_q_dim_first_jet_add»;
     «candle_cv_q_dim_first_jet_f»;
     «candle_cv_q_dim_first_jet_fixed_round»;
     «candle_cv_q_dim_first_jet_gradient»;
     «candle_cv_q_dim_first_jet_make»;
     «candle_cv_q_dim_first_jet_zero»;
     «candle_cv_q_dim_interval_list_add»;
     «candle_cv_q_dim_interval_matrix_add»;
     «candle_cv_q_dim_interval_zero_matrix»;
     «candle_cv_q_dim_interval_zeros»;
     «candle_cv_q_dim_jet_sqrt_d»;
     «candle_cv_q_dim_jet_sqrt_dd»;
     «candle_cv_q_dim_taylor_model_error»;
     «candle_cv_q_dim_taylor_model_gradient_bounds»;
     «candle_cv_q_dim_taylor_model_result_add»;
     «candle_cv_q_dim_taylor_model_result_center»;
     «candle_cv_q_dim_taylor_model_result_complete»;
     «candle_cv_q_dim_taylor_model_result_complete_rounded»;
     «candle_cv_q_dim_taylor_model_result_default»;
     «candle_cv_q_dim_taylor_model_result_domain»;
     «candle_cv_q_dim_taylor_model_result_gradient_bounds»;
     «candle_cv_q_dim_taylor_model_result_hessian»;
     «candle_cv_q_dim_taylor_model_result_make»;
     «candle_cv_q_dim_taylor_model_result_value_bound»;
     «candle_cv_q_dim_taylor_model_value_bound»;
     «candle_cv_q_dot_abs_upper_extended»;
     «candle_cv_q_fixed_interval_list_round»;
     «candle_cv_q_fixed_interval_matrix_round»;
     «candle_cv_q_fixed_interval_round»;
     «candle_cv_q_fixed_make»;
     «candle_cv_q_fixed_round_lower»;
     «candle_cv_q_fixed_round_upper»;
     «candle_cv_q_half»;
     «candle_cv_q_interval_add»;
     «candle_cv_q_interval_add_extended»;
     «candle_cv_q_interval_add_normalized»;
     «candle_cv_q_interval_inv»;
     «candle_cv_q_interval_mul»;
     «candle_cv_q_interval_mul_normalized»;
     «candle_cv_q_interval_neg»;
     «candle_cv_q_interval_normalize»;
     «candle_cv_q_interval_not_zero»;
     «candle_cv_q_interval_sqrt_certificate»;
     «candle_cv_q_inv»;
     «candle_cv_q_le»;
     «candle_cv_q_max»;
     «candle_cv_q_max4»;
     «candle_cv_q_min»;
     «candle_cv_q_min4»;
     «candle_cv_q_mul»;
     «candle_cv_q_mul_normalized_extended»;
     «candle_cv_q_neg»;
     «candle_cv_q_normalize»;
     «candle_cv_q_normalize_divide»;
     «candle_cv_q_normalize_extended»;
     «candle_cv_q_normalize_fallback»;
     «candle_cv_q_normalize_signed»;
     «candle_cv_q_normalize_signed_extended»;
     «candle_cv_q_normalize_verified»;
     «candle_cv_q_symmetric_interval»;
     «candle_cv_q_taylor_model_scale»;
     «candle_cv_q_weighted_rows_abs_upper_extended»;
     «candle_cv_q_zero»;
     «candle_cv_q_zero_interval»;
     «candle_cv_q_zmul»]
End

Theorem registered_case10173_tag10_ordinary_old_closed:
  compute_ceqs_closed_on registered_case10173_tag10_ordinary_reachable
    registered_case10173_historical_chunk16_ceqs
Proof
  irule compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem registered_case10173_tag10_ordinary_new_closed:
  compute_ceqs_closed_on registered_case10173_tag10_ordinary_reachable
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  irule compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem registered_case10173_tag10_ordinary_avoids_delta:
  EVERY
    (\function.
       function <> «candle_cv_fso_program_step_fixed_nonlinear» /\
       function <> «candle_cv_case10173_hist_splice_aux» /\
       function <> «candle_cv_case10173_hist_step»)
    registered_case10173_tag10_ordinary_reachable
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_ordinary_agree:
  compute_ceqs_agree_on registered_case10173_tag10_ordinary_reachable
    registered_case10173_historical_chunk16_ceqs
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  rw [compute_ceqs_agree_on_def]
  >> irule
       compute_registeredCase10173Tag10EnvironmentDeltaTheory.registered_case10173_tag10_lookup_unchanged
  >> mp_tac registered_case10173_tag10_ordinary_avoids_delta
  >> simp [EVERY_MEM]
QED

Theorem registered_case10173_tag10_ordinary_eval_cong:
  compute_exp_uses_only registered_case10173_tag10_ordinary_reachable
      expression ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      expression (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      expression refs
Proof
  metis_tac
    [CONJUNCT1 compute_eval_restricted_cong,
     registered_case10173_tag10_ordinary_old_closed,
     registered_case10173_tag10_ordinary_new_closed,
     registered_case10173_tag10_ordinary_agree]
QED

val _ = export_theory ();
