(*****************************************************************************
 * Exact structural source-DAG preparation for the pinned case16594 program.
 *
 * This is DEVELOPMENT / NON-RELEASE machinery.  It gives the checked-word
 * performance experiment a source-authenticated schedule: only structurally
 * equal source expressions with the same declared specialization role share
 * an identity.  Numerical certificate equality is deliberately not part of
 * this preparation layer; the executor must validate it before reusing a
 * certificate-bearing result.
 *****************************************************************************)
Theory compute_boundedCase16594SourceDagPlan
Ancestors
  compute_boundedCase16594ProgramData
Libs
  bossLib preamble

Datatype:
  bounded_analytic_dag_node =
    BoundedAnalyticDagPolynomial
      (bounded_poly_instruction list) bounded_analytic_specialization
  | BoundedAnalyticDagSqrt num
  | BoundedAnalyticDagNeg num
  | BoundedAnalyticDagAdd num num
  | BoundedAnalyticDagMul num num
  | BoundedAnalyticDagSquare num
  | BoundedAnalyticDagInverse num
  | BoundedAnalyticDagAtan num
  | BoundedAnalyticDagPiHalf
End

Definition bounded_analytic_dag_lookup_def:
  bounded_analytic_dag_lookup node [] index = NONE /\
  bounded_analytic_dag_lookup node (candidate::rest) index =
    if node = candidate then SOME index
    else bounded_analytic_dag_lookup node rest (SUC index)
End

Definition bounded_analytic_dag_intern_def:
  bounded_analytic_dag_intern node nodes =
    case bounded_analytic_dag_lookup node nodes 0 of
    | SOME index => (index,nodes)
    | NONE => (LENGTH nodes,SNOC node nodes)
End

Definition bounded_analytic_dag_source_node_def:
  bounded_analytic_dag_source_node instruction role stack =
    if ¬bounded_analytic_specialization_ok instruction role then NONE
    else
      case instruction of
      | BoundedAnalyticPolynomial program =>
          SOME (BoundedAnalyticDagPolynomial program role,stack)
      | BoundedAnalyticSqrt =>
          (case stack of
           | child::rest => SOME (BoundedAnalyticDagSqrt child,rest)
           | _ => NONE)
      | BoundedAnalyticNeg =>
          (case stack of
           | child::rest => SOME (BoundedAnalyticDagNeg child,rest)
           | _ => NONE)
      | BoundedAnalyticAdd =>
          (case stack of
           | right::left::rest =>
               SOME (BoundedAnalyticDagAdd left right,rest)
           | _ => NONE)
      | BoundedAnalyticMul =>
          (case stack of
           | right::left::rest =>
               SOME (BoundedAnalyticDagMul left right,rest)
           | _ => NONE)
      | BoundedAnalyticSquare =>
          (case stack of
           | child::rest => SOME (BoundedAnalyticDagSquare child,rest)
           | _ => NONE)
      | BoundedAnalyticInverse =>
          (case stack of
           | child::rest => SOME (BoundedAnalyticDagInverse child,rest)
           | _ => NONE)
      | BoundedAnalyticAtan =>
          (case stack of
           | child::rest => SOME (BoundedAnalyticDagAtan child,rest)
           | _ => NONE)
      | BoundedAnalyticPiHalf =>
          SOME (BoundedAnalyticDagPiHalf,stack)
End

Definition bounded_analytic_dag_step_def:
  bounded_analytic_dag_step instruction role state =
    case state of
    | (stack,nodes,identities) =>
      case bounded_analytic_dag_source_node instruction role stack of
      | NONE => NONE
      | SOME (node,rest) =>
        case bounded_analytic_dag_intern node nodes of
        | (identity,next_nodes) =>
            SOME (identity::rest,next_nodes,SNOC identity identities)
End

Definition bounded_analytic_dag_prepare_def:
  bounded_analytic_dag_prepare [] [] state = SOME state /\
  bounded_analytic_dag_prepare
      (instruction::instructions) (role::roles) state =
    (case bounded_analytic_dag_step instruction role state of
     | NONE => NONE
     | SOME next =>
         bounded_analytic_dag_prepare instructions roles next) /\
  bounded_analytic_dag_prepare _ _ _ = NONE
End

Definition bounded_case16594_source_dag_plan_def:
  bounded_case16594_source_dag_plan =
    case bounded_analytic_dag_prepare bounded_case16594_program
      bounded_case16594_specializations ([],[],[]) of
    | SOME ([root],nodes,identities) => SOME (nodes,identities,root)
    | _ => NONE
End

Definition bounded_case16594_source_dag_nodes_def:
  bounded_case16594_source_dag_nodes =
    case bounded_case16594_source_dag_plan of
    | SOME (nodes,identities,root) => nodes
    | NONE => []
End

Definition bounded_case16594_source_dag_identities_def:
  bounded_case16594_source_dag_identities =
    case bounded_case16594_source_dag_plan of
    | SOME (nodes,identities,root) => identities
    | NONE => []
End

Definition bounded_case16594_source_dag_root_def:
  bounded_case16594_source_dag_root =
    case bounded_case16594_source_dag_plan of
    | SOME (nodes,identities,root) => root
    | NONE => 0
End

Definition bounded_case16594_source_dag_plan_ok_def:
  bounded_case16594_source_dag_plan_ok ⇔
    bounded_case16594_source_dag_plan =
      SOME (bounded_case16594_source_dag_nodes,
            bounded_case16594_source_dag_identities,
            bounded_case16594_source_dag_root) /\
    LENGTH bounded_case16594_source_dag_nodes = 76 /\
    LENGTH bounded_case16594_source_dag_identities = 167 /\
    bounded_case16594_source_dag_root = 75 /\
    EVERY (\identity. identity < 76)
      bounded_case16594_source_dag_identities
End

Theorem bounded_case16594_source_dag_plan_ok_value:
  bounded_case16594_source_dag_plan_ok
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_source_dag_plan_counts:
  LENGTH bounded_case16594_source_dag_identities -
    LENGTH bounded_case16594_source_dag_nodes = 91
Proof
  EVAL_TAC
QED

Theorem bounded_analytic_dag_rejects_role_aliases:
  bounded_analytic_dag_source_node
    (BoundedAnalyticPolynomial (REPLICATE 39 BoundedPolyNeg))
    (BoundedNegDeltaDerivative 3) [] = NONE /\
  bounded_analytic_dag_prepare
    [BoundedAnalyticPolynomial
      (THE (bounded_analytic_specialization_program
        (BoundedNegDeltaDerivative 3)))] [] ([],[],[]) = NONE /\
  bounded_analytic_dag_prepare []
    [BoundedNegDeltaDerivative 3] ([],[],[]) = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
