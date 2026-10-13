(*****************************************************************************
 * Exact genuine-case regression for the general proved fast evaluator.
 *
 * This reuses the independently saved 271-equation evaluation theorem.  It
 * checks that the evaluator now installed in the Candle kernel recognizes the
 * same complete call and returns the exact expected cv value; its general
 * refinement theorem supplies the theorem-producing authority.
 *****************************************************************************)
Theory compute_pureFastCase10173Cell0Test
Ancestors
  compute_pureFast
  compute_registeredCase10173Cell0Eval
Libs
  bossLib preamble

Theorem registered_case10173_cell0_pure_fast_eval_value:
  compute_pure_fast_eval registered_case10173_cell0_ceqs
      registered_case10173_cell0_cexp =
    SOME registered_case10173_cell0_result
Proof
  simp [compute_pure_fast_eval_def,
        compute_pure_fast_fuel_def,
        registered_case10173_cell0_pure_eval_value]
QED

Theorem registered_case10173_cell0_pure_fast_refines_compute_eval:
  !s.
    compute_eval compute_default_clock registered_case10173_cell0_ceqs
      registered_case10173_cell0_cexp s =
    (M_success (from_cv registered_case10173_cell0_result),s)
Proof
  gen_tac
  >> assume_tac compute_pure_fast_eval_ok
  >> fs [computeTheory.compute_fast_eval_ok_def]
  >> first_x_assum irule
  >> simp [registered_case10173_cell0_pure_fast_eval_value]
QED

val _ = export_theory ();
