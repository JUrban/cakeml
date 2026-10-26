(*****************************************************************************
 * Reachability-authenticated congruence for the historical case-10173 item.
 *
 * The corrected equation environment changes three definitions outside the
 * historical item's transitive call graph.  The closed-list checks below are
 * evaluated by HOL over both exact generated environments; the semantic
 * congruence theorem then transfers the already-proved item evaluation
 * without re-running its expensive generic computation.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10HistItemCongruence
Ancestors
  compute_evalRestrictedCongruence
  compute_execProof
  compute_registeredCase10173HistoricalChunk16Data
  compute_registeredCase10173HistoricalChunk16Tag10Data
  compute_registeredCase10173Tag10EnvironmentDelta
Libs
  bossLib preamble

Definition registered_case10173_hist_item_reachable_def:
  registered_case10173_hist_item_reachable : mlstring list =
    [     «candle_cv_case10173_hist_item»;
     «candle_cv_fs_add»;
     «candle_cv_fs_angle_delta_gradient»;
     «candle_cv_fs_angle_delta_hessian»;
     «candle_cv_fs_angle_delta_value»;
     «candle_cv_fs_angle_interval_mul»;
     «candle_cv_fs_angle_interval_scale»;
     «candle_cv_fs_angle_interval_scale_neg_two»;
     «candle_cv_fs_angle_interval_sum»;
     «candle_cv_fs_angle_matrix_lookup»;
     «candle_cv_fs_angle_seven»;
     «candle_cv_fs_angle_six»;
     «candle_cv_fs_angle_ten»;
     «candle_cv_fs_canonical»;
     «candle_cv_fs_ceil_div»;
     «candle_cv_fs_dot_abs_upper»;
     «candle_cv_fs_first_gradient»;
     «candle_cv_fs_first_make»;
     «candle_cv_fs_first_value»;
     «candle_cv_fs_floor_div»;
     «candle_cv_fs_gradient_bounds»;
     «candle_cv_fs_hist_atan_interval»;
     «candle_cv_fs_hist_atan_lower_point»;
     «candle_cv_fs_hist_atan_pos_lower»;
     «candle_cv_fs_hist_atan_pos_upper»;
     «candle_cv_fs_hist_atan_upper_point»;
     «candle_cv_fs_hist_b_hessian»;
     «candle_cv_fs_hist_b_hessian_entry»;
     «candle_cv_fs_hist_b_hessian_row»;
     «candle_cv_fs_hist_c_vector»;
     «candle_cv_fs_hist_delta_gradient_block_0»;
     «candle_cv_fs_hist_delta_gradient_block_1»;
     «candle_cv_fs_hist_delta_gradient_block_2»;
     «candle_cv_fs_hist_delta_gradient_block_3»;
     «candle_cv_fs_hist_delta_gradient_block_4»;
     «candle_cv_fs_hist_delta_gradient_block_5»;
     «candle_cv_fs_hist_delta_gradient_component_block»;
     «candle_cv_fs_hist_delta_gradient_sign_entry»;
     «candle_cv_fs_hist_delta_second»;
     «candle_cv_fs_hist_delta_value_block»;
     «candle_cv_fs_hist_delta_x4_gradient»;
     «candle_cv_fs_hist_delta_x4_hessian»;
     «candle_cv_fs_hist_delta_x4_second»;
     «candle_cv_fs_hist_delta_x4_value»;
     «candle_cv_fs_hist_delta_x4_value_block»;
     «candle_cv_fs_hist_final_hessian»;
     «candle_cv_fs_hist_final_hessian_entry»;
     «candle_cv_fs_hist_final_hessian_row»;
     «candle_cv_fs_hist_final_hessian_symmetric_entry»;
     «candle_cv_fs_hist_first_order»;
     «candle_cv_fs_hist_four»;
     «candle_cv_fs_hist_log_u_gradient»;
     «candle_cv_fs_hist_log_u_gradient_entry»;
     «candle_cv_fs_hist_matrix_scale»;
     «candle_cv_fs_hist_monotone_coordinate»;
     «candle_cv_fs_hist_monotone_environment»;
     «candle_cv_fs_hist_point»;
     «candle_cv_fs_hist_positive_inv»;
     «candle_cv_fs_hist_rational_constant»;
     «candle_cv_fs_hist_raw_cubic»;
     «candle_cv_fs_hist_raw_product»;
     «candle_cv_fs_hist_replace_three»;
     «candle_cv_fs_hist_round_scale»;
     «candle_cv_fs_hist_second_gradient»;
     «candle_cv_fs_hist_second_hessian»;
     «candle_cv_fs_hist_second_make»;
     «candle_cv_fs_hist_second_order»;
     «candle_cv_fs_hist_second_sqrt_supplied»;
     «candle_cv_fs_hist_second_value»;
     «candle_cv_fs_hist_sqrt_hessian»;
     «candle_cv_fs_hist_sqrt_hessian_entry»;
     «candle_cv_fs_hist_sqrt_hessian_row»;
     «candle_cv_fs_hist_sqrt_hessian_symmetric_entry»;
     «candle_cv_fs_hist_three»;
     «candle_cv_fs_hist_u126»;
     «candle_cv_fs_hist_u135»;
     «candle_cv_fs_hist_u_points»;
     «candle_cv_fs_hist_u_three»;
     «candle_cv_fs_hist_u_value_formula»;
     «candle_cv_fs_interval_abs_upper»;
     «candle_cv_fs_interval_add»;
     «candle_cv_fs_interval_list_of_q»;
     «candle_cv_fs_interval_lookup»;
     «candle_cv_fs_interval_neg»;
     «candle_cv_fs_interval_of_q»;
     «candle_cv_fs_interval_one»;
     «candle_cv_fs_interval_zero»;
     «candle_cv_fs_list_of_q»;
     «candle_cv_fs_neg»;
     «candle_cv_fs_of_q_lower»;
     «candle_cv_fs_of_q_upper»;
     «candle_cv_fs_one»;
     «candle_cv_fs_raw_abs»;
     «candle_cv_fs_raw_add»;
     «candle_cv_fs_raw_interval_add»;
     «candle_cv_fs_raw_interval_list_round»;
     «candle_cv_fs_raw_interval_list_scale»;
     «candle_cv_fs_raw_interval_matrix_round»;
     «candle_cv_fs_raw_interval_matrix_scale»;
     «candle_cv_fs_raw_interval_mul»;
     «candle_cv_fs_raw_interval_round»;
     «candle_cv_fs_raw_le»;
     «candle_cv_fs_raw_max»;
     «candle_cv_fs_raw_min»;
     «candle_cv_fs_raw_mul»;
     «candle_cv_fs_raw_neg»;
     «candle_cv_fs_raw_scale»;
     «candle_cv_fs_result_complete_rounded»;
     «candle_cv_fs_result_make»;
     «candle_cv_fs_scale»;
     «candle_cv_fs_scale_squared»;
     «candle_cv_fs_two_scale_squared»;
     «candle_cv_fs_weighted_rows_abs_upper»;
     «candle_cv_fs_zero»;
     «candle_cv_fsa_item_fixed»;
     «candle_cv_fsn_interval_list_scale»;
     «candle_cv_q_ceil_div»;
     «candle_cv_q_den»;
     «candle_cv_q_fixed_make»;
     «candle_cv_q_fixed_round_lower»;
     «candle_cv_q_fixed_round_upper»;
     «candle_cv_q_pi_half_interval»;
     «candle_cv_q_taylor_model_scale»]
End

Theorem registered_case10173_hist_item_reachable_count:
  LENGTH registered_case10173_hist_item_reachable = 123
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_item_old_closed:
  compute_ceqs_closed_on registered_case10173_hist_item_reachable
    registered_case10173_historical_chunk16_ceqs
Proof
  irule compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem registered_case10173_hist_item_tag10_closed:
  compute_ceqs_closed_on registered_case10173_hist_item_reachable
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  irule compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem registered_case10173_hist_item_reachable_avoids_tag10_delta:
  EVERY
    (\function.
       function <> «candle_cv_fso_program_step_fixed_nonlinear» /\
       function <> «candle_cv_case10173_hist_splice_aux» /\
       function <> «candle_cv_case10173_hist_step»)
    registered_case10173_hist_item_reachable
Proof
  EVAL_TAC
QED

Theorem registered_case10173_hist_item_old_tag10_lookup:
  MEM function_name registered_case10173_hist_item_reachable ==>
  ALOOKUP registered_case10173_historical_chunk16_ceqs function_name =
    ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs function_name
Proof
  strip_tac
  >> `function_name <> «candle_cv_fso_program_step_fixed_nonlinear» /\
      function_name <> «candle_cv_case10173_hist_splice_aux» /\
      function_name <> «candle_cv_case10173_hist_step»` by
    (mp_tac registered_case10173_hist_item_reachable_avoids_tag10_delta
     >> simp [EVERY_MEM]
     >> metis_tac [])
  >> metis_tac
       [compute_registeredCase10173Tag10EnvironmentDeltaTheory.registered_case10173_tag10_lookup_unchanged]
QED

Theorem registered_case10173_hist_item_old_tag10_agree:
  compute_ceqs_agree_on registered_case10173_hist_item_reachable
    registered_case10173_historical_chunk16_ceqs
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  rw [compute_ceqs_agree_on_def]
  >> metis_tac [registered_case10173_hist_item_old_tag10_lookup]
QED

Theorem registered_case10173_hist_item_call_uses_only:
  compute_exp_uses_only registered_case10173_hist_item_reachable
    (App «candle_cv_case10173_hist_item»
      [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
Proof
  simp
    [registered_case10173_hist_item_reachable_def,
     compute_exp_uses_only_def,
     cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv]
QED

Theorem registered_case10173_hist_item_old_tag10_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_case10173_hist_item»
      [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
    (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_item»
      [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
    refs
Proof
  metis_tac
    [CONJUNCT1 compute_eval_restricted_cong,
     registered_case10173_hist_item_call_uses_only,
     registered_case10173_hist_item_old_closed,
     registered_case10173_hist_item_tag10_closed,
     registered_case10173_hist_item_old_tag10_agree]
QED

val _ = export_theory ();
