(*****************************************************************************
 * Symbolic semantic trace for the first authenticated case-16594 object
 * instruction.
 *
 * The exact object evaluator stores rational intervals without requiring a
 * canonical representation.  Reducing its concrete intermediate states can
 * therefore manufacture very large denominators even when the mathematical
 * value is zero.  This theory keeps the result symbolic and independent of
 * the production evaluator graph: it evaluates the corresponding object-q
 * relation and fixes the cv encoding of the resulting Taylor state.  A small
 * join theory authenticates the production source and representation later.
 * This split keeps semantic proof iteration independent of evaluator builds.
 *****************************************************************************)
open compute_boundedAnalyticObjectPolyRunRefinementTheory
open compute_boundedPackedObjectEntryContractTheory
open preamble

Theory compute_boundedCase16594ObjectFirstPolySemantic
Ancestors
  compute_boundedAnalyticObjectPolyRunRefinement
  compute_boundedPackedObjectEntryContract
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_object_semantic_state_cv_def:
  bounded_case16594_object_semantic_state_cv domain_cv center_value
      center_gradient value_bound gradient_bounds packed_hessian =
    Pair domain_cv
      (Pair center_value
        (Pair center_gradient
          (Pair value_bound (Pair gradient_bounds packed_hessian))))
End

Definition bounded_case16594_object_taylor_state_cv_def:
  bounded_case16594_object_taylor_state_cv
      (BoundedObjectQTaylor domain center_value center_gradient value_bound
        gradient_bounds packed_hessian) =
    bounded_case16594_object_semantic_state_cv
      (if domain then Num 1 else Num 0)
      center_value
      (bounded_object_q_cv_list center_gradient)
      value_bound
      (bounded_object_q_cv_list gradient_bounds)
      (bounded_object_q_cv_list packed_hessian)
End

Definition bounded_case16594_object_taylor_stack_cv_def:
  bounded_case16594_object_taylor_stack_cv [] = Num 0 /\
  bounded_case16594_object_taylor_stack_cv (object_state::object_states) =
    Pair (bounded_case16594_object_taylor_state_cv object_state)
      (bounded_case16594_object_taylor_stack_cv object_states)
End

Definition bounded_case16594_object_source0_poly_program_def:
  bounded_case16594_object_source0_poly_program =
    [BoundedPolyConstant 1 0 0;
     BoundedPolyConstant 13 0 499;
     BoundedPolyNeg;
     BoundedPolyMul]
End

Definition bounded_case16594_object_cell0_word_radii_def:
  bounded_case16594_object_cell0_word_radii : word64 list =
    [161518258122w; 161518258122w; 161518258122w;
     323036516242w; 211308954991w; 323036516242w]
End

Definition bounded_case16594_object_cell0_weights_def:
  bounded_case16594_object_cell0_weights =
    THE
      (bounded_taylor_radius_pairs
        bounded_case16594_object_cell0_word_radii)
End

Definition bounded_case16594_object_source0_result_def:
  bounded_case16594_object_source0_result =
    bounded_object_q_taylor_mul
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      (bounded_object_q_taylor_constant 1 0 0)
      (bounded_object_q_taylor_neg
        bounded_case16594_object_cell0_word_radii
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_constant 13 0 499))
End

Theorem bounded_case16594_object_cell0_radius_pairs:
  bounded_taylor_radius_pairs bounded_case16594_object_cell0_word_radii =
    SOME bounded_case16594_object_cell0_weights
Proof
  simp
    [bounded_case16594_object_cell0_word_radii_def,
     bounded_case16594_object_cell0_weights_def,
     compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def]
QED

Theorem bounded_case16594_object_source0_semantic_trace:
  bounded_object_q_poly_run
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      object_center_environment object_box_environment
      bounded_case16594_object_source0_poly_program [] =
    SOME [bounded_case16594_object_source0_result]
Proof
  simp
    [bounded_case16594_object_source0_poly_program_def,
     bounded_case16594_object_source0_result_def,
     compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
QED

Theorem bounded_case16594_object_source0_result_runtime_shape:
  ?domain center_value center_gradient value_bound gradient_bounds
      packed_hessian.
    bounded_case16594_object_source0_result =
      BoundedObjectQTaylor domain center_value center_gradient value_bound
        gradient_bounds packed_hessian /\
    bounded_case16594_object_taylor_state_cv
        bounded_case16594_object_source0_result =
      bounded_case16594_object_semantic_state_cv
        (if domain then Num 1 else Num 0)
        center_value
        (bounded_object_q_cv_list center_gradient)
        value_bound
        (bounded_object_q_cv_list gradient_bounds)
        (bounded_object_q_cv_list packed_hessian)
Proof
  Cases_on `bounded_case16594_object_source0_result`
  >> simp [bounded_case16594_object_taylor_state_cv_def]
QED

val _ = export_theory ();
