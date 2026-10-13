(*****************************************************************************
 * Verified evaluation of the exact genuine case-10173 cell-0 wrapper call.
 *
 * This is an offline proof-producing bridge experiment.  The first-order
 * evaluator is translated to cv equations, so evaluating this theorem does
 * not expand the 271-function environment with the simplifier.
 *****************************************************************************)
Theory compute_registeredCase10173Cell0Eval
Ancestors
  compute_evalPure
  compute_registeredCase10173Cell0Data
Libs
  bossLib preamble cv_transLib

val _ = cv_trans registered_case10173_cell0_ceqs_def;
val _ = cv_trans registered_case10173_cell0_cexp_def;

val registered_case10173_cell0_pure_eval =
  time cv_eval
    ``compute_eval_pure 100000 registered_case10173_cell0_ceqs
        registered_case10173_cell0_cexp``;

val _ = save_thm
  ("registered_case10173_cell0_pure_eval",
   registered_case10173_cell0_pure_eval);

Theorem registered_case10173_cell0_pure_eval_value:
  compute_eval_pure 100000 registered_case10173_cell0_ceqs
      registered_case10173_cell0_cexp =
    SOME (from_cv registered_case10173_cell0_result)
Proof
  simp [registered_case10173_cell0_pure_eval,
        registered_case10173_cell0_result_def,
        compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
