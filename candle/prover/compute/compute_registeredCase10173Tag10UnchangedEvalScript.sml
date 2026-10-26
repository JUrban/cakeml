(*****************************************************************************
 * Evaluator congruence for the shared, unchanged structural support used by
 * the corrected tag-10 case-10173 checker.  The list is the transitive union
 * of the root/guard, source-patching, rational-handoff, center and radius
 * call graphs.  Its closure and exact agreement are checked against both
 * generated equation tables below.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10UnchangedEval
Ancestors
  compute_evalRestrictedCongruence
  compute_execProof
  compute_registeredCase10173HistoricalChunk16Data
  compute_registeredCase10173HistoricalChunk16Tag10Data
  compute_registeredCase10173Tag10EnvironmentDelta
Libs
  bossLib preamble

Definition registered_case10173_tag10_unchanged_reachable_def:
  registered_case10173_tag10_unchanged_reachable : mlstring list =
    [«candle_cv_analytic_instruction_is_sqrt»;
     «candle_cv_analytic_instruction_patch_sqrt»;
     «candle_cv_analytic_program_patch_sqrt»;
     «candle_cv_analytic_program_sqrt_data_exact»;
     «candle_cv_case10173_hist_production_guard»;
     «candle_cv_case10173_hist_root_inputs»;
     «candle_cv_case10173_hist_root_record_check»;
     «candle_cv_fs_add»;
     «candle_cv_fs_angle_delta_hessian»;
     «candle_cv_fs_angle_delta_value»;
     «candle_cv_fs_angle_interval_mul»;
     «candle_cv_fs_angle_interval_scale»;
     «candle_cv_fs_angle_interval_scale_neg_two»;
     «candle_cv_fs_angle_interval_sum»;
     «candle_cv_fs_angle_seven»;
     «candle_cv_fs_angle_six»;
     «candle_cv_fs_angle_ten»;
     «candle_cv_fs_canonical»;
     «candle_cv_fs_ceil_div»;
     «candle_cv_fs_first_gradient»;
     «candle_cv_fs_first_value»;
     «candle_cv_fs_floor_div»;
     «candle_cv_fs_hist_bool_and»;
     «candle_cv_fs_hist_bool_not»;
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
     «candle_cv_fs_hist_environment_nonnegative»;
     «candle_cv_fs_hist_four»;
     «candle_cv_fs_hist_monotone_coordinate»;
     «candle_cv_fs_hist_monotone_environment»;
     «candle_cv_fs_hist_num_le»;
     «candle_cv_fs_hist_point»;
     «candle_cv_fs_hist_positive_interval»;
     «candle_cv_fs_hist_positive_inv»;
     «candle_cv_fs_hist_positive_product»;
     «candle_cv_fs_hist_positive_root_certificate»;
     «candle_cv_fs_hist_quotient»;
     «candle_cv_fs_hist_raw_cubic»;
     «candle_cv_fs_hist_raw_product»;
     «candle_cv_fs_hist_root_certificate»;
     «candle_cv_fs_hist_root_list_check»;
     «candle_cv_fs_hist_round_scale»;
     «candle_cv_fs_hist_second_make»;
     «candle_cv_fs_hist_second_value»;
     «candle_cv_fs_hist_three»;
     «candle_cv_fs_hist_u126»;
     «candle_cv_fs_hist_u135»;
     «candle_cv_fs_hist_u_points»;
     «candle_cv_fs_hist_u_three»;
     «candle_cv_fs_hist_u_value_formula»;
     «candle_cv_fs_hist_unit_interval»;
     «candle_cv_fs_interval_add»;
     «candle_cv_fs_interval_list_of_q»;
     «candle_cv_fs_interval_list_to_q»;
     «candle_cv_fs_interval_lookup»;
     «candle_cv_fs_interval_matrix_to_q»;
     «candle_cv_fs_interval_neg»;
     «candle_cv_fs_interval_of_q»;
     «candle_cv_fs_interval_one»;
     «candle_cv_fs_interval_to_q»;
     «candle_cv_fs_interval_zero»;
     «candle_cv_fs_neg»;
     «candle_cv_fs_of_q_lower»;
     «candle_cv_fs_of_q_upper»;
     «candle_cv_fs_one»;
     «candle_cv_fs_raw_add»;
     «candle_cv_fs_raw_interval_mul»;
     «candle_cv_fs_raw_interval_round»;
     «candle_cv_fs_raw_le»;
     «candle_cv_fs_raw_max»;
     «candle_cv_fs_raw_min»;
     «candle_cv_fs_raw_mul»;
     «candle_cv_fs_raw_neg»;
     «candle_cv_fs_raw_scale»;
     «candle_cv_fs_result_center»;
     «candle_cv_fs_result_domain»;
     «candle_cv_fs_result_gradient_bounds»;
     «candle_cv_fs_result_hessian»;
     «candle_cv_fs_result_to_q»;
     «candle_cv_fs_result_value_bound»;
     «candle_cv_fs_scale»;
     «candle_cv_fs_scale_squared»;
     «candle_cv_fs_to_q»;
     «candle_cv_fs_zero»;
     «candle_cv_fsa_item_is_fixed»;
     «candle_cv_fsa_item_payload»;
     «candle_cv_fsa_item_to_q»;
     «candle_cv_fso_variable_job_canonical»;
     «candle_cv_fso_variable_jobs_canonical»;
     «candle_cv_lc_num_canonical»;
     «candle_cv_lc_z_canonical»;
     «candle_cv_lc_zadd»;
     «candle_cv_lc_zscale»;
     «candle_cv_q_add»;
     «candle_cv_q_box_valid_list»;
     «candle_cv_q_canonical»;
     «candle_cv_q_ceil_div»;
     «candle_cv_q_center_environment_list»;
     «candle_cv_q_den»;
     «candle_cv_q_den_product_pred»;
     «candle_cv_q_dim_first_jet_make»;
     «candle_cv_q_dim_taylor_model_certified_finish»;
     «candle_cv_q_dim_taylor_model_certified_upper»;
     «candle_cv_q_dim_taylor_model_result_domain»;
     «candle_cv_q_dim_taylor_model_result_make»;
     «candle_cv_q_dim_taylor_model_result_value_bound»;
     «candle_cv_q_dim_whole_box_finish»;
     «candle_cv_q_fixed_list_round_upper»;
     «candle_cv_q_fixed_make»;
     «candle_cv_q_fixed_round_lower»;
     «candle_cv_q_fixed_round_upper»;
     «candle_cv_q_half»;
     «candle_cv_q_interval_canonical»;
     «candle_cv_q_interval_list_canonical»;
     «candle_cv_q_le»;
     «candle_cv_q_midpoint»;
     «candle_cv_q_mul»;
     «candle_cv_q_neg»;
     «candle_cv_q_point_interval»;
     «candle_cv_q_radius»;
     «candle_cv_q_radius_list»;
     «candle_cv_q_taylor_model_scale»;
     «candle_cv_q_zero»;
     «candle_cv_q_zmul»]
End

Theorem registered_case10173_tag10_unchanged_old_closed:
  compute_ceqs_closed_on registered_case10173_tag10_unchanged_reachable
    registered_case10173_historical_chunk16_ceqs
Proof
  irule compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem registered_case10173_tag10_unchanged_new_closed:
  compute_ceqs_closed_on registered_case10173_tag10_unchanged_reachable
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  irule compute_ceqs_closed_on_from_every
  >> EVAL_TAC
QED

Theorem registered_case10173_tag10_unchanged_avoids_delta:
  EVERY
    (\function.
       function <> «candle_cv_fso_program_step_fixed_nonlinear» /\
       function <> «candle_cv_case10173_hist_splice_aux» /\
       function <> «candle_cv_case10173_hist_step»)
    registered_case10173_tag10_unchanged_reachable
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_unchanged_agree:
  compute_ceqs_agree_on registered_case10173_tag10_unchanged_reachable
    registered_case10173_historical_chunk16_ceqs
    registered_case10173_historical_chunk16_tag10_ceqs
Proof
  rw [compute_ceqs_agree_on_def]
  >> irule
       compute_registeredCase10173Tag10EnvironmentDeltaTheory.registered_case10173_tag10_lookup_unchanged
  >> mp_tac registered_case10173_tag10_unchanged_avoids_delta
  >> simp [EVERY_MEM]
QED

Theorem registered_case10173_tag10_unchanged_eval_cong:
  compute_exp_uses_only registered_case10173_tag10_unchanged_reachable
      expression ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      expression (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      expression refs
Proof
  metis_tac
    [CONJUNCT1 compute_eval_restricted_cong,
     registered_case10173_tag10_unchanged_old_closed,
     registered_case10173_tag10_unchanged_new_closed,
     registered_case10173_tag10_unchanged_agree]
QED

val _ = export_theory ();
