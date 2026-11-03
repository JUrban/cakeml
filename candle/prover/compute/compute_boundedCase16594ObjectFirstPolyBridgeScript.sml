(*****************************************************************************
 * Join the independently built exact evaluator and object-q semantics for
 * the first authenticated case-16594 polynomial source.
 *
 * Keep source/radius authentication and representation alignment here so the
 * symbolic semantic theory remains independent of the evaluator build graph.
 *****************************************************************************)
open compute_boundedCase16594ObjectFirstPolyEvalTheory
open compute_boundedCase16594ObjectFirstPolySemanticTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolyBridge
Ancestors
  compute_boundedCase16594ObjectFirstPolyEval
  compute_boundedCase16594ObjectFirstPolySemantic
Libs
  bossLib preamble wordsLib

Theorem bounded_case16594_object_semantic_state_cv_identity:
  bounded_case16594_object_semantic_state_cv domain_cv center_value
      center_gradient value_bound gradient_bounds packed_hessian =
    bounded_case16594_object_state_cv domain_cv center_value center_gradient
      value_bound gradient_bounds packed_hessian
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_semantic_state_cv_def,
     compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def]
QED

Theorem bounded_case16594_object_taylor_state_production_shape:
  bounded_case16594_object_taylor_state_cv
      (BoundedObjectQTaylor object_domain center_value center_gradient
        value_bound gradient_bounds packed_hessian) =
    bounded_case16594_object_state_cv
      (if object_domain then Num 1 else Num 0)
      center_value
      (bounded_object_q_cv_list center_gradient)
      value_bound
      (bounded_object_q_cv_list gradient_bounds)
      (bounded_object_q_cv_list packed_hessian)
Proof
  simp
    [compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_taylor_state_cv_def,
     bounded_case16594_object_semantic_state_cv_identity]
QED

Theorem bounded_case16594_object_cell0_radii_equivalent:
  bounded_object_q_cv_list_decode
      bounded_case16594_object_cell0_radii_cv <> NONE /\
  LIST_REL bounded_case10173_q_cv_equiv
    (THE
      (bounded_object_q_cv_list_decode
        bounded_case16594_object_cell0_radii_cv))
    (MAP bounded_word64_object_q_cv
      bounded_case16594_object_cell0_word_radii)
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_radii_cv_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_word_radii_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_decode_def,
     compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
     compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_def,
     compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_def,
     compute_boundedObjectIntervalRelationTheory.bounded_object_signed_int_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_source0_decodes:
  bounded_analytic_instruction_of_cv
      bounded_case16594_object_cell0_source0_cv =
    SOME
      (BoundedAnalyticPolynomial
        bounded_case16594_object_source0_poly_program)
Proof
  simp
    [compute_boundedCase16594ObjectDispatchPrefix8EvalTheory.bounded_case16594_object_cell0_source0_cv_def,
     compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_source0_poly_program_def,
     compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_poly_program_of_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_poly_instruction_of_cv_def,
     compute_boundedAnalyticProgramCVTheory.bounded_rational_of_cv_def]
QED

val _ = export_theory ();
