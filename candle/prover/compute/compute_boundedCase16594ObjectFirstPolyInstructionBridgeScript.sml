(*****************************************************************************
 * Authenticated semantic/evaluator vertical slice for the first genuine
 * case-16594 instruction.
 *
 * The source decoder, symbolic object-q step, production CV evaluator, and
 * representation-independent final state were proved separately.  This
 * theory joins those facts without replaying the large numerical evaluator.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolyStateBridgeTheory
open compute_boundedCase16594ObjectFirstPolyBridgeTheory
open compute_boundedCase16594ObjectFirstPolyEvalTheory
open compute_boundedCase16594ObjectFirstPolySemanticTheory
open compute_boundedAnalyticObjectProgramStepRefinementTheory
open compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolyInstructionBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyStateBridge
  compute_boundedCase16594ObjectFirstPolyBridge
  compute_boundedCase16594ObjectFirstPolyEval
  compute_boundedAnalyticObjectProgramStepRefinement
  compute_boundedCase16594ObjectDispatchProgramTraceEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_source0_ordinary_semantic_step:
  bounded_object_q_analytic_ordinary_step
    bounded_case16594_object_cell0_word_radii
    bounded_case16594_object_cell0_weights
    object_center_environment object_box_environment
    (BoundedAnalyticPolynomial
      bounded_case16594_object_source0_poly_program)
    (object_stack,certificates)
    (bounded_case16594_object_source0_result::object_stack,certificates)
Proof
  simp
    [bounded_object_q_analytic_ordinary_step_def,
     bounded_case16594_object_source0_semantic_trace]
QED

Theorem bounded_case16594_object_source0_dispatch_step_eval_above:
  bounded_case16594_object_dispatch_step_eval_above 16391
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    (Num 0) bounded_case16594_object_cell0_source0_cv
    certificates stack
    (Pair bounded_case16594_object_first_mul_result_cv stack)
    certificates
Proof
  rw [bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_source0_dispatch_step_eval)
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_source0_authenticated_instruction_bridge:
  bounded_object_q_cv_list_decode
      bounded_case16594_object_cell0_radii_cv <> NONE /\
  LIST_REL bounded_case10173_q_cv_equiv
    (THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_radii_cv))
    (MAP bounded_word64_object_q_cv
      bounded_case16594_object_cell0_word_radii) /\
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source0_cv =
    SOME
      (BoundedAnalyticPolynomial
        bounded_case16594_object_source0_poly_program) /\
  bounded_object_q_analytic_ordinary_step
    bounded_case16594_object_cell0_word_radii
    bounded_case16594_object_cell0_weights
    object_center_environment object_box_environment
    (BoundedAnalyticPolynomial
      bounded_case16594_object_source0_poly_program)
    (object_stack,certificates)
    (bounded_case16594_object_source0_result::object_stack,certificates) /\
  bounded_case16594_object_dispatch_step_eval_above 16391
    center_boxes outer_boxes bounded_case16594_object_cell0_radii_cv
    (Num 0) bounded_case16594_object_cell0_source0_cv
    runtime_certificates runtime_stack
    (Pair bounded_case16594_object_first_mul_result_cv runtime_stack)
    runtime_certificates /\
  bounded_object_q_taylor_runtime_equiv
    bounded_case16594_object_first_mul_result_cv
    bounded_case16594_object_source0_result
Proof
  simp
    [bounded_case16594_object_cell0_radii_equivalent,
     bounded_case16594_object_source0_decodes,
     bounded_case16594_object_source0_ordinary_semantic_step,
     bounded_case16594_object_source0_dispatch_step_eval_above,
     bounded_case16594_object_first_mul_runtime_semantic_equiv]
QED

val _ = export_theory ();
