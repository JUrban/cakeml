(*****************************************************************************
 * First genuine proof-producing gate for the registered fast NL route.
 *
 * The registration key is the complete structural identity produced by the
 * existing Kernel.compute parser: exact reachable equations plus exact call.
 * A hit executes the complete checked-word case-10173 cell checker.  Its
 * result is authoritative only because the theorem below proves that result
 * equal to the existing verified evaluator on this exact registered call.
 *****************************************************************************)
Theory compute_registeredCase10173Cell0Fast
Ancestors
  compute_registeredCase10173Cell0Eval
  compute_boundedCase10173HistoricalCell0Data
Libs
  bossLib preamble wordsLib

Definition registered_case10173_cell0_fast_eval_def:
  registered_case10173_cell0_fast_eval ceqs cexp =
    if ceqs = registered_case10173_cell0_ceqs /\
       cexp = registered_case10173_cell0_cexp
    then
      if bounded_case10173_cell0_check ()
      then SOME registered_case10173_cell0_result
      else NONE
    else NONE
End

Theorem registered_case10173_cell0_compute_eval:
  !s.
    compute_eval compute_default_clock registered_case10173_cell0_ceqs
      registered_case10173_cell0_cexp s =
    (M_success (from_cv registered_case10173_cell0_result),s)
Proof
  gen_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `100000`
  >> simp [computeTheory.compute_default_clock,
           registered_case10173_cell0_pure_eval_value]
QED

Theorem registered_case10173_cell0_fast_eval_ok:
  compute_fast_eval_ok registered_case10173_cell0_fast_eval
Proof
  rw [computeTheory.compute_fast_eval_ok_def,
      registered_case10173_cell0_fast_eval_def]
  >> every_case_tac
  >> gvs [bounded_case10173_cell0_check_value,
          registered_case10173_cell0_compute_eval]
QED

val _ = export_theory ();
