(*****************************************************************************
 * Proof-only schedule bridge for the exact case16594 source DAG.
 *
 * The executable checker consumes prepared instructions and identities.  This
 * validator ties every such pair back to the original source instruction,
 * declared specialization role, structural DAG node, and identity-stack
 * transition.  It is deliberately outside the recurring executable path.
 *****************************************************************************)
Theory compute_boundedCase16594SourceDagSound
Ancestors
  compute_boundedCase16594SourceDagEval
Libs
  bossLib preamble wordsLib

Definition bounded_analytic64_dag_schedule_step_def:
  bounded_analytic64_dag_schedule_step nodes source role prepared identity
      identity_stack =
    case bounded_case16594_compile_specialized_instruction source role of
    | NONE => NONE
    | SOME expected_prepared =>
        if expected_prepared <> prepared then NONE
        else
          case bounded_analytic_dag_source_node source role identity_stack of
          | NONE => NONE
          | SOME (expected_node,rest) =>
              case oEL identity nodes of
              | NONE => NONE
              | SOME authenticated_node =>
                  if authenticated_node = expected_node then
                    SOME (identity::rest)
                  else NONE
End

Definition bounded_analytic64_dag_schedule_run_def:
  bounded_analytic64_dag_schedule_run nodes [] [] [] [] identity_stack =
      SOME identity_stack /\
  bounded_analytic64_dag_schedule_run nodes
      (source::sources) (role::roles) (prepared::prepareds)
      (identity::identities) identity_stack =
    (case bounded_analytic64_dag_schedule_step nodes source role prepared
        identity identity_stack of
     | NONE => NONE
     | SOME next_stack =>
         bounded_analytic64_dag_schedule_run nodes sources roles prepareds
           identities next_stack) /\
  bounded_analytic64_dag_schedule_run nodes _ _ _ _ _ = NONE
End

Definition bounded_case16594_source_dag_schedule_ok_def:
  bounded_case16594_source_dag_schedule_ok <=>
    bounded_case16594_prepared_program_ok /\
    bounded_case16594_source_dag_plan_ok /\
    bounded_analytic64_dag_schedule_run
      bounded_case16594_source_dag_nodes bounded_case16594_program
      bounded_case16594_specializations bounded_case16594_prepared_program
      bounded_case16594_source_dag_identities [] =
        SOME [bounded_case16594_source_dag_root]
End

Theorem bounded_case16594_source_dag_schedule_ok_value:
  bounded_case16594_source_dag_schedule_ok
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Definition bounded_analytic_dag_node_children_def:
  bounded_analytic_dag_node_children node =
    case node of
    | BoundedAnalyticDagPolynomial program role => []
    | BoundedAnalyticDagSqrt child => [child]
    | BoundedAnalyticDagNeg child => [child]
    | BoundedAnalyticDagAdd left right => [left;right]
    | BoundedAnalyticDagMul left right => [left;right]
    | BoundedAnalyticDagSquare child => [child]
    | BoundedAnalyticDagInverse child => [child]
    | BoundedAnalyticDagAtan child => [child]
    | BoundedAnalyticDagPiHalf => []
End

Definition bounded_analytic_dag_nodes_topological_from_def:
  bounded_analytic_dag_nodes_topological_from index [] = T /\
  bounded_analytic_dag_nodes_topological_from index (node::nodes) =
    (EVERY (\child. child < index)
      (bounded_analytic_dag_node_children node) /\
     bounded_analytic_dag_nodes_topological_from (SUC index) nodes)
End

Definition bounded_analytic64_dag_stack_refines_def:
  bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache <=>
    LIST_REL
      (\identity value.
         oEL identity result_cache = SOME (SOME value))
      identity_stack value_stack
End

Theorem bounded_case16594_source_dag_nodes_topological:
  bounded_analytic_dag_nodes_topological_from 0
    bounded_case16594_source_dag_nodes
Proof
  EVAL_TAC
QED

Theorem bounded_analytic64_dag_stack_refines_empty:
  bounded_analytic64_dag_stack_refines [] [] result_cache
Proof
  simp [bounded_analytic64_dag_stack_refines_def]
QED

Theorem bounded_analytic64_dag_stack_refines_cons:
  bounded_analytic64_dag_stack_refines (identity::identity_stack)
      (value::value_stack) result_cache <=>
    oEL identity result_cache = SOME (SOME value) /\
    bounded_analytic64_dag_stack_refines identity_stack value_stack
      result_cache
Proof
  simp [bounded_analytic64_dag_stack_refines_def]
QED

Theorem bounded_analytic64_dag_schedule_rejects_prepared_alias:
  bounded_analytic64_dag_schedule_step
    [BoundedAnalyticDagPiHalf] BoundedAnalyticPiHalf
    BoundedAnalyticGeneral BoundedAnalytic64Neg 0 [] = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_analytic64_dag_schedule_rejects_identity_alias:
  bounded_analytic64_dag_schedule_step
    [BoundedAnalyticDagPiHalf;BoundedAnalyticDagNeg 0]
    BoundedAnalyticPiHalf BoundedAnalyticGeneral
    BoundedAnalytic64PiHalf 1 [] = NONE
Proof
  EVAL_TAC
QED

Theorem bounded_analytic64_dag_schedule_rejects_role_alias:
  bounded_analytic64_dag_schedule_step
    [BoundedAnalyticDagPolynomial
      (THE (bounded_analytic_specialization_program
        (BoundedNegDeltaDerivative 3))) BoundedAnalyticGeneral]
    (BoundedAnalyticPolynomial
      (THE (bounded_analytic_specialization_program
        (BoundedNegDeltaDerivative 3))))
    (BoundedNegDeltaDerivative 3)
    (BoundedAnalytic64NegDeltaDerivative 3) 0 [] = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
