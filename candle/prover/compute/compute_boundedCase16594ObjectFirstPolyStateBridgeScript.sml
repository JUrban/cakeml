(*****************************************************************************
 * Complete representation-independent state bridge for the first genuine
 * case-16594 polynomial instruction.
 *
 * The large production fields and the symbolic object-q semantics are proved
 * independently.  This theory only composes their compact field theorems, so
 * changes to the semantic bridge never replay the production evaluator.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolyValueBridgeTheory
open compute_boundedCase16594ObjectFirstPolySemanticShapeTheory
open compute_boundedObjectTaylorEquivalenceTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolyStateBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyValueBridge
  compute_boundedCase16594ObjectFirstPolySemanticShape
  compute_boundedObjectTaylorEquivalence
Libs
  bossLib preamble

Theorem bounded_case16594_object_first_value_bound_semantic_equiv:
  bounded_object_q_interval_cv_equiv
    bounded_case16594_object_first_result_value_bound_cv
    (bounded_object_q_taylor_value_bound
      bounded_case16594_object_source0_result)
Proof
  irule bounded_object_q_interval_cv_equiv_trans
  >> qexists_tac `bounded_analytic_source_q_interval_cv 0 13 499`
  >> conj_tac
  >- ACCEPT_TAC bounded_case16594_object_first_value_bound_expected_equiv
  >> irule bounded_object_q_interval_cv_equiv_trans
  >> qexists_tac `bounded_case16594_object_first_result_center_cv`
  >> conj_tac
  >- (irule bounded_object_q_interval_cv_equiv_sym
      >> ACCEPT_TAC bounded_case16594_object_first_center_expected_equiv)
  >> irule bounded_object_q_interval_cv_equiv_trans
  >> qexists_tac
       `bounded_object_q_taylor_center
          bounded_case16594_object_source0_result`
  >> conj_tac
  >- ACCEPT_TAC
       compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory.bounded_case16594_object_first_center_semantic_equiv
  >> irule bounded_object_q_interval_cv_equiv_sym
  >> ACCEPT_TAC bounded_case16594_object_source0_value_bound_center_equiv
QED

Theorem bounded_case16594_object_first_gradient_bounds_semantic_equiv:
  bounded_object_q_interval_list_cv_equiv
    bounded_case16594_object_first_result_gradient_bounds_cv
    (bounded_object_q_cv_list
      (bounded_object_q_taylor_gradient_bounds
        bounded_case16594_object_source0_result))
Proof
  irule bounded_object_q_interval_list_cv_equiv_trans
  >> qexists_tac
       `bounded_object_q_cv_list
          (REPLICATE 6
            (bounded_analytic_source_q_interval_cv 0 0 0))`
  >> simp
    [compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory.bounded_case16594_object_first_gradient_bounds_zero_equiv,
     bounded_case16594_object_source0_gradient_bounds_zero_equiv]
QED

Theorem bounded_case16594_object_first_hessian_semantic_equiv:
  bounded_object_q_interval_list_cv_equiv
    bounded_case16594_object_first_result_hessian_cv
    (bounded_object_q_cv_list
      (bounded_object_q_taylor_hessian
        bounded_case16594_object_source0_result))
Proof
  irule bounded_object_q_interval_list_cv_equiv_trans
  >> qexists_tac
       `bounded_object_q_cv_list
          (REPLICATE 21
            (bounded_analytic_source_q_interval_cv 0 0 0))`
  >> simp
    [compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory.bounded_case16594_object_first_hessian_zero_equiv,
     bounded_case16594_object_source0_hessian_zero_equiv]
QED

Theorem bounded_case16594_object_first_mul_runtime_semantic_equiv:
  bounded_object_q_taylor_runtime_equiv
    bounded_case16594_object_first_mul_result_cv
    bounded_case16594_object_source0_result
Proof
  rewrite_tac
    [compute_boundedCase16594ObjectFirstPolyResultFieldsTheory.bounded_case16594_object_first_result_fields,
     compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
     bounded_object_q_taylor_runtime_equiv_selectors]
  >> simp
    [compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory.bounded_case16594_object_first_domain_matches,
     compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory.bounded_case16594_object_first_center_semantic_equiv,
     compute_boundedCase16594ObjectFirstPolyFieldBridgeTheory.bounded_case16594_object_first_center_gradient_semantic_equiv,
     bounded_case16594_object_first_value_bound_semantic_equiv,
     bounded_case16594_object_first_gradient_bounds_semantic_equiv,
     bounded_case16594_object_first_hessian_semantic_equiv]
QED

val _ = export_theory ();
