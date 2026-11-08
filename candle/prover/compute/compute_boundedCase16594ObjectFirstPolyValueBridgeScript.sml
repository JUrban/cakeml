(*****************************************************************************
 * Isolated value-bound bridge for the first genuine object polynomial.
 *
 * This obligation contains the largest closed rational in the first state.
 * Keep it separate from the already-green field bridge and use cv_compute so
 * failed experiments never replay the center/gradient/Hessian proofs.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolyValueBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyFieldBridge
Libs
  bossLib preamble cv_transLib

val _ = cv_trans
  compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_cv_equiv_direct_def;
val _ = cv_trans
  compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_direct_def;
val _ = cv_trans
  compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def;
val _ = cv_trans
  compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_interval_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_value_bound_cv_def;
val _ = cv_trans
  compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_center_cv_def;

Theorem bounded_case16594_object_first_center_expected_direct:
  bounded_object_q_interval_cv_equiv_direct
    bounded_case16594_object_first_result_center_cv
    (bounded_analytic_source_q_interval_cv 0 13 499)
Proof
  CONV_TAC cv_eval
QED

Theorem bounded_case16594_object_first_center_expected_equiv:
  bounded_object_q_interval_cv_equiv
    bounded_case16594_object_first_result_center_cv
    (bounded_analytic_source_q_interval_cv 0 13 499)
Proof
  rewrite_tac
    [GSYM compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_direct_correct]
  >> ACCEPT_TAC bounded_case16594_object_first_center_expected_direct
QED

Theorem bounded_case16594_object_first_value_bound_expected_direct:
  bounded_object_q_interval_cv_equiv_direct
    bounded_case16594_object_first_result_value_bound_cv
    (bounded_analytic_source_q_interval_cv 0 13 499)
Proof
  CONV_TAC cv_eval
QED

Theorem bounded_case16594_object_first_value_bound_expected_equiv:
  bounded_object_q_interval_cv_equiv
    bounded_case16594_object_first_result_value_bound_cv
    (bounded_analytic_source_q_interval_cv 0 13 499)
Proof
  rewrite_tac
    [GSYM compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_direct_correct]
  >> ACCEPT_TAC bounded_case16594_object_first_value_bound_expected_direct
QED

val _ = export_theory ();
