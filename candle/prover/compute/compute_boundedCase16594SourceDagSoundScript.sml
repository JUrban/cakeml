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
