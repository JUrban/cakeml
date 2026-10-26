Theory compute_registeredCase10173Tag10StructuralCongruence
Ancestors
  compute_registeredCase10173Tag10UnchangedEval
  compute_registeredCase10173Tag10OrdinaryStepCongruence
Libs
  bossLib preamble

Theorem registered_case10173_tag10_center_environment_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_q_center_environment_list» [from_cv boxes])
    (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_q_center_environment_list» [from_cv boxes]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_radius_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_q_fixed_list_round_upper»
      [App «candle_cv_q_radius_list» [from_cv boxes]])
    (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_q_fixed_list_round_upper»
      [App «candle_cv_q_radius_list» [from_cv boxes]]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_item_head_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_fsa_item_head»
      [from_cv center_boxes;from_cv boxes;from_cv stack])
    (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_fsa_item_head»
      [from_cv center_boxes;from_cv boxes;from_cv stack]) refs
Proof
  irule
    compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_item_to_q_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_fsa_item_to_q» [from_cv item])
    (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_fsa_item_to_q» [from_cv item]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_root_record_check_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_case10173_hist_root_record_check»
      [from_cv boxes;from_cv root_record]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_root_record_check»
      [from_cv boxes;from_cv root_record]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_production_guard_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_case10173_hist_production_guard»
      [from_cv boxes;from_cv root_record]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_production_guard»
      [from_cv boxes;from_cv root_record]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_sqrt_data_exact_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_analytic_program_sqrt_data_exact»
      [from_cv sqrt_data;from_cv source_program]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_analytic_program_sqrt_data_exact»
      [from_cv sqrt_data;from_cv source_program]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_patch_sqrt_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_analytic_program_patch_sqrt»
      [from_cv sqrt_data;from_cv source_program]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_analytic_program_patch_sqrt»
      [from_cv sqrt_data;from_cv source_program]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_certified_finish_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_q_dim_taylor_model_certified_finish»
      [from_cv boxes;from_cv result]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_q_dim_taylor_model_certified_finish»
      [from_cv boxes;from_cv result]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_variable_jobs_canonical_eval_cong:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_fso_variable_jobs_canonical» [from_cv encoded_jobs])
    (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_fso_variable_jobs_canonical» [from_cv encoded_jobs]) refs
Proof
  irule
    compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_eval_cong
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10UnchangedEvalTheory.registered_case10173_tag10_unchanged_reachable_def,
        compute_registeredCase10173Tag10OrdinaryStepCongruenceTheory.registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

val _ = export_theory ();
