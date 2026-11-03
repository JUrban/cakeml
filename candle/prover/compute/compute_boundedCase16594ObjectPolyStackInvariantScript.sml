(*****************************************************************************
 * Strong runtime/semantic invariant for production object-q polynomial
 * stacks.
 *
 * Numerical equivalence alone is not enough to invoke the production
 * operation bridges: subsequent steps also need the fixed six-/twenty-one-
 * field shape and packed-interval validity.  This theory records those facts
 * once and establishes the two stack-producing base cases.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyStackInvariant
Ancestors
  compute_boundedCase16594ObjectPolyBaseStepSemanticEval
  compute_boundedCase16594ObjectPolyVariableStepSemanticEval
Libs
  bossLib preamble intLib

Definition bounded_object_q_taylor_semantic_valid_def:
  bounded_object_q_taylor_semantic_valid
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) <=>
    bounded_packed_q_interval_valid_cv center /\
    EVERY bounded_packed_q_interval_valid_cv center_gradient /\
    LENGTH center_gradient = 6 /\
    bounded_packed_q_interval_valid_cv value_bound /\
    EVERY bounded_packed_q_interval_valid_cv gradient_bounds /\
    LENGTH gradient_bounds = 6 /\
    EVERY bounded_packed_q_interval_valid_cv hessian /\
    LENGTH hessian = 21
End

Definition bounded_object_q_taylor_runtime_refines_def:
  bounded_object_q_taylor_runtime_refines runtime semantic <=>
    bounded_object_q_taylor_runtime_equiv runtime semantic /\
    bounded_object_q_taylor_semantic_valid semantic
End

Definition bounded_object_q_taylor_stack_runtime_refines_def:
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack <=>
    LIST_REL bounded_object_q_taylor_runtime_refines
      runtime_stack semantic_stack
End

Theorem bounded_object_q_taylor_constant_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  simp
    [bounded_object_q_taylor_semantic_valid_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_analytic_source_q_interval_valid,
     compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_zero]
QED

Theorem bounded_object_q_taylor_constant_runtime_refines:
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_constant_state_cv
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  simp
    [bounded_object_q_taylor_runtime_refines_def,
     bounded_object_q_taylor_constant_semantic_valid,
     compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_constant_runtime_semantic_equiv]
QED

Theorem bounded_object_q_unit_vector_semantic_valid:
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_unit_vector variable) /\
  LENGTH (bounded_object_q_unit_vector variable) = 6
Proof
  simp
    [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_unit_vector_def,
     EVERY_GENLIST]
  >> rpt COND_CASES_TAC
  >> simp
       [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_analytic_source_q_interval_valid]
QED

Theorem bounded_object_q_taylor_variable_semantic_valid:
  EVERY bounded_packed_q_interval_valid_cv center_environment /\
  LENGTH center_environment = 6 /\
  EVERY bounded_packed_q_interval_valid_cv box_environment /\
  LENGTH box_environment = 6 /\
  variable < 6 ==>
  bounded_object_q_taylor_semantic_valid
    (THE
      (bounded_object_q_taylor_variable
        center_environment box_environment variable))
Proof
  strip_tac
  >> `bounded_object_q_nth center_environment variable =
        SOME (EL variable center_environment)` by
       (irule
          compute_boundedCase16594ObjectVariableStateEvalTheory.bounded_case16594_object_nth_el
        >> intLib.ARITH_TAC)
  >> `bounded_object_q_nth box_environment variable =
        SOME (EL variable box_environment)` by
       (irule
          compute_boundedCase16594ObjectVariableStateEvalTheory.bounded_case16594_object_nth_el
        >> intLib.ARITH_TAC)
  >> `bounded_packed_q_interval_valid_cv
        (EL variable center_environment) /\
      bounded_packed_q_interval_valid_cv
        (EL variable box_environment)` by
       metis_tac [EVERY_EL]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_variable_def,
        bounded_object_q_taylor_semantic_valid_def,
        bounded_object_q_unit_vector_semantic_valid,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_zero]
QED

Theorem bounded_object_q_taylor_variable_runtime_refines:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  variable < 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes ==>
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_variable_state_cv
      runtime_center_boxes runtime_outer_boxes variable)
    (THE
      (bounded_object_q_taylor_variable
        semantic_center_boxes semantic_outer_boxes variable))
Proof
  strip_tac
  >> `LENGTH semantic_center_boxes = 6 /\
      LENGTH semantic_outer_boxes = 6` by
       metis_tac [LIST_REL_LENGTH]
  >> simp [bounded_object_q_taylor_runtime_refines_def]
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectVariableStateEvalTheory.bounded_case16594_object_variable_state_runtime_semantic_equiv
      >> simp [])
  >> irule bounded_object_q_taylor_variable_semantic_valid
  >> simp []
QED

val _ = export_theory ();
