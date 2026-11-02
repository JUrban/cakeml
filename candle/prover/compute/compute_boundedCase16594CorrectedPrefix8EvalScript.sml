(*****************************************************************************
 * Proof-producing check of the corrected case-16594 center prefix 8.       *
 *****************************************************************************)
Theory compute_boundedCase16594CorrectedPrefix8Eval
Ancestors
  compute_evalPure
  compute_boundedCase16594CorrectedPrefix8Data
Libs
  bossLib preamble cv_transLib

val _ = cv_trans bounded_case16594_corrected_prefix8_ceqs_def;
val _ = cv_trans bounded_case16594_corrected_prefix8_cexp_def;

val bounded_case16594_corrected_prefix8_eval =
  time cv_eval
    ``compute_eval_pure 1000000
        bounded_case16594_corrected_prefix8_ceqs
        bounded_case16594_corrected_prefix8_cexp``;

val _ = save_thm
  ("bounded_case16594_corrected_prefix8_eval",
   bounded_case16594_corrected_prefix8_eval);
val _ = print_thm bounded_case16594_corrected_prefix8_eval;

val _ = export_theory ();
