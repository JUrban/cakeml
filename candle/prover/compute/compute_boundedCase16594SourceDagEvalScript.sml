(*****************************************************************************
 * Certificate-preserving exact source-DAG executor.
 *
 * DEVELOPMENT / NON-RELEASE.  A cached result may be reused only at the
 * exact source identity computed by compute_boundedCase16594SourceDagPlan.
 * For square root, inverse, and arctangent nodes, the current certificate
 * must equal the certificate that was checked when the cached result was
 * first produced.  Thus cache reuse cannot silently skip a changed witness.
 *****************************************************************************)
Theory compute_boundedCase16594SourceDagEval
Ancestors
  compute_boundedCase16594PreparedPlan
  compute_boundedCase16594SourceDagPlan
Libs
  bossLib preamble wordsLib

Definition bounded_analytic64_instruction_arity_def:
  bounded_analytic64_instruction_arity instruction =
    case instruction of
    | BoundedAnalytic64Polynomial program => 0
    | BoundedAnalytic64NegDeltaDerivative coordinate => 0
    | BoundedAnalytic64FourCoordinateDelta coordinate => 0
    | BoundedAnalytic64Sqrt => 1
    | BoundedAnalytic64Neg => 1
    | BoundedAnalytic64Add => 2
    | BoundedAnalytic64Mul => 2
    | BoundedAnalytic64Square => 1
    | BoundedAnalytic64Inverse => 1
    | BoundedAnalytic64Atan => 1
    | BoundedAnalytic64PiHalf => 0
End

Definition bounded_analytic64_instruction_uses_certificate_def:
  bounded_analytic64_instruction_uses_certificate instruction =
    case instruction of
    | BoundedAnalytic64Sqrt => T
    | BoundedAnalytic64Inverse => T
    | BoundedAnalytic64Atan => T
    | _ => F
End

Definition bounded_analytic64_current_certificate_def:
  bounded_analytic64_current_certificate instruction certificates =
    if bounded_analytic64_instruction_uses_certificate instruction then
      case certificates of
      | certificate::rest => SOME (SOME certificate,rest)
      | [] => NONE
    else SOME (NONE,certificates)
End

Definition bounded_analytic64_reuse_stack_def:
  bounded_analytic64_reuse_stack value arity stack =
    if arity = 0 then SOME (value::stack)
    else if arity = 1 then
      case stack of
      | operand::rest => SOME (value::rest)
      | _ => NONE
    else if arity = 2 then
      case stack of
      | right::left::rest => SOME (value::rest)
      | _ => NONE
    else NONE
End

Definition bounded_analytic64_dag_step_def:
  bounded_analytic64_dag_step radii center_environment box_environment
      instruction identity state =
    case state of
    | (stack,certificates,result_cache,certificate_cache) =>
      if identity >= LENGTH result_cache ∨
         LENGTH certificate_cache <> LENGTH result_cache then NONE
      else
        case bounded_analytic64_current_certificate instruction
          certificates of
        | NONE => NONE
        | SOME (current_certificate,certificate_rest) =>
          case oEL identity result_cache of
          | SOME (SOME cached_result) =>
              if oEL identity certificate_cache <>
                 SOME current_certificate then NONE
              else
                (case bounded_analytic64_reuse_stack cached_result
                    (bounded_analytic64_instruction_arity instruction)
                    stack of
                 | NONE => NONE
                 | SOME next_stack =>
                     SOME (next_stack,certificate_rest,
                           result_cache,certificate_cache))
          | SOME NONE =>
              (case bounded_analytic64_program_step radii
                  center_environment box_environment instruction
                  (stack,certificates) of
               | NONE => NONE
               | SOME (next_stack,next_certificates) =>
                   case next_stack of
                   | [] => NONE
                   | result::rest =>
                       SOME (next_stack,next_certificates,
                         LUPDATE (SOME result) identity result_cache,
                         LUPDATE current_certificate identity
                           certificate_cache))
          | NONE => NONE
End

Definition bounded_analytic64_dag_run_def:
  bounded_analytic64_dag_run radii center_environment box_environment
      [] [] state = SOME state /\
  bounded_analytic64_dag_run radii center_environment box_environment
      (instruction::instructions) (identity::identities) state =
    (case bounded_analytic64_dag_step radii center_environment
       box_environment instruction identity state of
     | NONE => NONE
     | SOME next =>
         bounded_analytic64_dag_run radii center_environment
           box_environment instructions identities next) /\
  bounded_analytic64_dag_run radii center_environment box_environment
      _ _ _ = NONE
End

Definition bounded_analytic64_dag_eval_def:
  bounded_analytic64_dag_eval radii center_environment box_environment
      program identities cache_size certificates =
    case bounded_analytic64_dag_run radii center_environment box_environment
      program identities
      ([],certificates,REPLICATE cache_size NONE,
       REPLICATE cache_size NONE) of
    | SOME ([result],[],result_cache,certificate_cache) => SOME result
    | _ => NONE
End

Definition bounded_case16594_source_dag_eval_def:
  bounded_case16594_source_dag_eval radii center_environment
      box_environment certificates =
    if ¬bounded_case16594_prepared_program_ok ∨
       ¬bounded_case16594_source_dag_plan_ok then NONE
    else
      bounded_analytic64_dag_eval radii center_environment box_environment
        bounded_case16594_prepared_program
        bounded_case16594_source_dag_identities
        (LENGTH bounded_case16594_source_dag_nodes) certificates
End

(* The executable boundary uses the closed, proved plan directly.  Keeping
   the cache size literal avoids rebuilding the closed node list per cell;
   the equality theorem below ties this form back to the checked wrapper. *)
Definition bounded_case16594_source_dag_eval_fast_def:
  bounded_case16594_source_dag_eval_fast radii center_environment
      box_environment certificates =
    bounded_analytic64_dag_eval radii center_environment box_environment
      bounded_case16594_prepared_program
      bounded_case16594_source_dag_identities 76 certificates
End

Theorem bounded_case16594_source_dag_eval_fast_eq:
  bounded_case16594_source_dag_eval radii center_environment
      box_environment certificates =
    bounded_case16594_source_dag_eval_fast radii center_environment
      box_environment certificates
Proof
  assume_tac bounded_case16594_source_dag_plan_ok_value
  >> fs [bounded_case16594_source_dag_eval_def,
         bounded_case16594_source_dag_eval_fast_def,
         compute_boundedCase16594PreparedPlanTheory.bounded_case16594_prepared_program_ok_value,
         bounded_case16594_source_dag_plan_ok_def]
QED

Theorem bounded_analytic64_dag_certificate_reuse_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let zero = bounded_interval64_zero in
  let constant = BoundedAnalytic64Polynomial
    [BoundedTaylor64Constant one] in
  let inverse = BoundedAnalytic64InverseCertificate one one in
  let changed = BoundedAnalytic64InverseCertificate one zero in
  IS_SOME
    (bounded_analytic64_dag_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one)
      [constant;BoundedAnalytic64Inverse;
       constant;BoundedAnalytic64Inverse;BoundedAnalytic64Add]
      [0;1;0;1;2] 3 [inverse;inverse]) /\
  bounded_analytic64_dag_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one)
      [constant;BoundedAnalytic64Inverse;
       constant;BoundedAnalytic64Inverse;BoundedAnalytic64Add]
      [0;1;0;1;2] 3 [inverse;changed] = NONE /\
  bounded_analytic64_dag_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [constant] [3] 3 [] = NONE /\
  bounded_analytic64_dag_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [constant] [] 3 [] = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
