(*****************************************************************************
 * Incremental CV translation of the corrected tag-10 equation environment.
 * Reuse the translated historical table and translate only its three exact
 * replacement entries; an evaluated equality ties the result to the literal
 * generated tag-10 table.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10EnvironmentCV
Ancestors
  compute_registeredCase10173Tag10EnvironmentDelta
  compute_registeredCase10173GenuineProgramMemoEval
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_tag10_step_fixed_entry_def:
  registered_case10173_tag10_step_fixed_entry :
      mlstring list # compute_exp =
    THE (ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_fso_program_step_fixed_nonlinear»)
End

Definition registered_case10173_tag10_splice_entry_def:
  registered_case10173_tag10_splice_entry : mlstring list # compute_exp =
    THE (ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_splice_aux»)
End

Definition registered_case10173_tag10_hist_step_entry_def:
  registered_case10173_tag10_hist_step_entry : mlstring list # compute_exp =
    THE (ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_step»)
End

val registered_case10173_tag10_step_fixed_entry_value =
  EVAL ``registered_case10173_tag10_step_fixed_entry``;
val _ = save_thm
  ("registered_case10173_tag10_step_fixed_entry_value",
   registered_case10173_tag10_step_fixed_entry_value);
val _ = cv_trans registered_case10173_tag10_step_fixed_entry_value;

val registered_case10173_tag10_splice_entry_value =
  EVAL ``registered_case10173_tag10_splice_entry``;
val _ = save_thm
  ("registered_case10173_tag10_splice_entry_value",
   registered_case10173_tag10_splice_entry_value);
val _ = cv_trans registered_case10173_tag10_splice_entry_value;

val registered_case10173_tag10_hist_step_entry_value =
  EVAL ``registered_case10173_tag10_hist_step_entry``;
val _ = save_thm
  ("registered_case10173_tag10_hist_step_entry_value",
   registered_case10173_tag10_hist_step_entry_value);
val _ = cv_trans registered_case10173_tag10_hist_step_entry_value;

Definition registered_case10173_replace_ceq_entry_def:
  registered_case10173_replace_ceq_entry key replacement [] = [] /\
  registered_case10173_replace_ceq_entry key replacement
      ((entry_key,entry_value)::rest) =
    if key = entry_key then (key,replacement)::rest
    else (entry_key,entry_value)::
      registered_case10173_replace_ceq_entry key replacement rest
End

val _ = cv_trans registered_case10173_replace_ceq_entry_def;

Definition registered_case10173_tag10_environment_cv_delta_def:
  registered_case10173_tag10_environment_cv_delta =
    registered_case10173_replace_ceq_entry
      «candle_cv_case10173_hist_step»
      registered_case10173_tag10_hist_step_entry
      (registered_case10173_replace_ceq_entry
        «candle_cv_case10173_hist_splice_aux»
        registered_case10173_tag10_splice_entry
        (registered_case10173_replace_ceq_entry
          «candle_cv_fso_program_step_fixed_nonlinear»
          registered_case10173_tag10_step_fixed_entry
          registered_case10173_historical_chunk16_ceqs))
End

Theorem registered_case10173_tag10_environment_cv_delta_exact:
  registered_case10173_historical_chunk16_tag10_ceqs =
    registered_case10173_tag10_environment_cv_delta
Proof
  EVAL_TAC
QED

val _ = cv_trans registered_case10173_tag10_environment_cv_delta_def;
val _ = cv_trans registered_case10173_tag10_environment_cv_delta_exact;

val _ = export_theory ();
