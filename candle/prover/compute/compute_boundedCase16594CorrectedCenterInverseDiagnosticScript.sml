(*****************************************************************************
 * Development-only diagnosis of the first inverse in the corrected genuine *
 * case-16594 cell-0 center replay.  This extracts the prefix-7 state from    *
 * the already checked prefix-8 fixture and reports both exact guard bits.    *
 *****************************************************************************)
Theory compute_boundedCase16594CorrectedCenterInverseDiagnostic
Ancestors
  compute_boundedCase16594CorrectedPrefix8Eval
Libs
  bossLib preamble cv_transLib

Definition bounded_case16594_corrected_center_exp_take_def:
  bounded_case16594_corrected_center_exp_take 0
      (expression:compute_exp) = Num 0 /\
  bounded_case16594_corrected_center_exp_take (SUC count)
      (Pair head tail) =
    Pair head (bounded_case16594_corrected_center_exp_take count tail) /\
  bounded_case16594_corrected_center_exp_take (SUC count) expression = Num 0
End

Definition bounded_case16594_corrected_center7_state_cexp_def:
  bounded_case16594_corrected_center7_state_cexp =
    case bounded_case16594_corrected_prefix8_cexp of
    | Pair
        (Uop Fst
          (App name [boxes;codes;sources;certificates;stack]))
        placeholder =>
        App name
          [boxes;
           bounded_case16594_corrected_center_exp_take 7 codes;
           bounded_case16594_corrected_center_exp_take 7 sources;
           certificates;
           stack]
    | _ => Num 0
End

Definition bounded_case16594_corrected_center7_result_cexp_def:
  bounded_case16594_corrected_center7_result_cexp =
    Uop Fst
      (Uop Fst
        (Uop Snd bounded_case16594_corrected_center7_state_cexp))
End

Definition bounded_case16594_corrected_center7_certificates_cexp_def:
  bounded_case16594_corrected_center7_certificates_cexp =
    Uop Snd
      (Uop Snd bounded_case16594_corrected_center7_state_cexp)
End

Definition bounded_case16594_corrected_center7_center_input_cexp_def:
  bounded_case16594_corrected_center7_center_input_cexp =
    App «candle_cv_q_dim_first_jet_f»
      [App «candle_cv_q_dim_taylor_model_result_center»
        [bounded_case16594_corrected_center7_result_cexp]]
End

Definition bounded_case16594_corrected_center7_box_input_cexp_def:
  bounded_case16594_corrected_center7_box_input_cexp =
    App «candle_cv_q_dim_jet_f»
      [App «candle_cv_q_dim_taylor_model_proxy»
        [bounded_case16594_corrected_center7_result_cexp]]
End

Definition bounded_case16594_corrected_center7_certificate0_cexp_def:
  bounded_case16594_corrected_center7_certificate0_cexp =
    Uop Fst bounded_case16594_corrected_center7_certificates_cexp
End

Definition bounded_case16594_corrected_center7_certificate1_cexp_def:
  bounded_case16594_corrected_center7_certificate1_cexp =
    Uop Fst
      (Uop Snd bounded_case16594_corrected_center7_certificates_cexp)
End

Definition bounded_case16594_corrected_center7_inverse_diagnostic_cexp_def:
  bounded_case16594_corrected_center7_inverse_diagnostic_cexp =
    Pair bounded_case16594_corrected_center7_center_input_cexp
      (Pair bounded_case16594_corrected_center7_box_input_cexp
        (Pair bounded_case16594_corrected_center7_certificate0_cexp
          (Pair bounded_case16594_corrected_center7_certificate1_cexp
            (Pair
              (App «candle_cv_q_interval_inv_certificate»
                [bounded_case16594_corrected_center7_center_input_cexp;
                 bounded_case16594_corrected_center7_certificate0_cexp])
              (App «candle_cv_q_interval_inv_certificate»
                [bounded_case16594_corrected_center7_box_input_cexp;
                 bounded_case16594_corrected_center7_certificate1_cexp])))))
End

val _ = cv_trans bounded_case16594_corrected_center_exp_take_def;
val _ = cv_trans bounded_case16594_corrected_center7_state_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_result_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_certificates_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_center_input_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_box_input_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_certificate0_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_certificate1_cexp_def;
val _ = cv_trans bounded_case16594_corrected_center7_inverse_diagnostic_cexp_def;

val bounded_case16594_corrected_center7_inverse_diagnostic_eval =
  time cv_eval
    ``compute_eval_pure 1000000
        bounded_case16594_corrected_prefix8_ceqs
        bounded_case16594_corrected_center7_inverse_diagnostic_cexp``;

val _ = save_thm
  ("bounded_case16594_corrected_center7_inverse_diagnostic_eval",
   bounded_case16594_corrected_center7_inverse_diagnostic_eval);
val _ = print_thm
  bounded_case16594_corrected_center7_inverse_diagnostic_eval;

val _ = export_theory ();
