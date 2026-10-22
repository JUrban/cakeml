(*****************************************************************************
 * Total postfix executor for prepared compact Taylor instructions.
 *
 * Source rational constants and analytic operations are compiled into this
 * small prepared language outside the hot loop.  The enclosing plan checker
 * must authenticate that compilation.  This executor itself is general,
 * shape-safe, overflow-aware, and independent of a particular Flyspeck
 * expression.
 *****************************************************************************)
Theory compute_boundedTaylorProgram
Ancestors
  compute_boundedTaylorBase
Libs
  bossLib preamble

Datatype:
  bounded_taylor64_instruction =
    BoundedTaylor64Constant bounded_interval64
  | BoundedTaylor64Variable num
  | BoundedTaylor64Neg
  | BoundedTaylor64Add
  | BoundedTaylor64Mul
  | BoundedTaylor64Square
End

Definition bounded_taylor64_stack_well_formed_def:
  bounded_taylor64_stack_well_formed stack ⇔
    EVERY bounded_taylor64_well_formed stack
End

(* Native HOL Light's Taylor evaluator completes additive results from their
 * center jet, Hessian, and box radii.  Reusing already-completed value bounds
 * here loses cancellations in large signed polynomials (notably delta).
 * These two general operations retain that normalization boundary. *)
Definition bounded_taylor64_neg_complete_def:
  bounded_taylor64_neg_complete radii source =
    if ¬bounded_taylor64_well_formed source then NONE else
    case source of
    | BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian =>
        bounded_taylor64_complete radii domain
          (bounded_interval64_neg center_value)
          (bounded_interval64_list_neg center_gradient)
          (bounded_interval64_list_neg hessian)
End

Definition bounded_taylor64_add_complete_def:
  bounded_taylor64_add_complete radii left right =
    if ¬bounded_taylor64_well_formed left ∨
       ¬bounded_taylor64_well_formed right
    then NONE else
    case left of
    | BoundedTaylor64 left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian =>
      case right of
      | BoundedTaylor64 right_domain right_center right_center_gradient
          right_value right_gradient_bounds right_hessian =>
        case bounded_interval64_add left_center right_center of
        | NONE => NONE
        | SOME center_value =>
          case bounded_interval64_list_add
            left_center_gradient right_center_gradient of
          | NONE => NONE
          | SOME center_gradient =>
            case bounded_interval64_list_add left_hessian right_hessian of
            | NONE => NONE
            | SOME hessian =>
                bounded_taylor64_complete radii
                  (left_domain ∧ right_domain) center_value
                  center_gradient hessian
End

Definition bounded_taylor64_program_step_def:
  bounded_taylor64_program_step radii center_environment box_environment
      instruction stack =
    case instruction of
    | BoundedTaylor64Constant value =>
        (case bounded_taylor64_constant value of
         | NONE => NONE
         | SOME result => SOME (result::stack))
    | BoundedTaylor64Variable index =>
        (case bounded_taylor64_variable
          center_environment box_environment index of
         | NONE => NONE
         | SOME result => SOME (result::stack))
    | BoundedTaylor64Neg =>
        (case stack of
         | value::rest =>
             (case bounded_taylor64_neg_complete radii value of
              | NONE => NONE
              | SOME result => SOME (result::rest))
         | _ => NONE)
    | BoundedTaylor64Add =>
        (case stack of
         | right::left::rest =>
             (case bounded_taylor64_add_complete radii left right of
              | NONE => NONE
              | SOME result => SOME (result::rest))
         | _ => NONE)
    | BoundedTaylor64Mul =>
        (case stack of
         | right::left::rest =>
             (case bounded_taylor64_mul radii left right of
              | NONE => NONE
              | SOME result => SOME (result::rest))
         | _ => NONE)
    | BoundedTaylor64Square =>
        (case stack of
         | value::rest =>
             (case bounded_taylor64_mul radii value value of
              | NONE => NONE
              | SOME result => SOME (result::rest))
         | _ => NONE)
End

Theorem bounded_taylor64_neg_complete_some:
  bounded_taylor64_neg_complete radii source = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_neg_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some
QED

Theorem bounded_taylor64_add_complete_some:
  bounded_taylor64_add_complete radii left right = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_add_complete_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedTaylorUnaryTheory.bounded_taylor64_complete_some
QED

Definition bounded_taylor64_program_run_def:
  bounded_taylor64_program_run radii center_environment box_environment
      [] stack = SOME stack ∧
  bounded_taylor64_program_run radii center_environment box_environment
      (instruction::instructions) stack =
    case bounded_taylor64_program_step radii center_environment
      box_environment instruction stack of
    | NONE => NONE
    | SOME next =>
        bounded_taylor64_program_run radii center_environment
          box_environment instructions next
End

Definition bounded_taylor64_program_eval_def:
  bounded_taylor64_program_eval radii center_environment box_environment
      program =
    case bounded_taylor64_program_run radii center_environment
      box_environment program [] of
    | SOME [result] => SOME result
    | _ => NONE
End

Theorem bounded_taylor64_program_step_well_formed:
  bounded_taylor64_stack_well_formed stack ∧
  bounded_taylor64_program_step radii center_environment box_environment
      instruction stack = SOME result ⇒
  bounded_taylor64_stack_well_formed result
Proof
  Cases_on `instruction`
  >> Cases_on `stack`
  >> rw [bounded_taylor64_program_step_def,
         bounded_taylor64_stack_well_formed_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_constant_some
  >> imp_res_tac bounded_taylor64_variable_some
  >> imp_res_tac bounded_taylor64_neg_complete_some
  >> imp_res_tac bounded_taylor64_add_complete_some
  >> imp_res_tac
       compute_boundedTaylorMulTheory.bounded_taylor64_mul_some
  >> fs [bounded_taylor64_stack_well_formed_def]
QED

Theorem bounded_taylor64_program_run_well_formed:
  ∀program stack result.
    bounded_taylor64_stack_well_formed stack ∧
    bounded_taylor64_program_run radii center_environment box_environment
      program stack = SOME result ⇒
    bounded_taylor64_stack_well_formed result
Proof
  Induct
  >> rw [bounded_taylor64_program_run_def]
  >> every_case_tac
  >> gvs []
  >> first_x_assum match_mp_tac
  >> metis_tac [bounded_taylor64_program_step_well_formed]
QED

Theorem bounded_taylor64_program_eval_some:
  bounded_taylor64_program_eval radii center_environment box_environment
      program = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  rw [bounded_taylor64_program_eval_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_taylor64_program_run_well_formed
  >> fs [bounded_taylor64_stack_well_formed_def]
QED

Theorem bounded_taylor64_program_closed_tests:
  let zeros6 = REPLICATE 6 bounded_interval64_zero in
  let zeros21 = REPLICATE 21 bounded_interval64_zero in
  let radii = REPLICATE 6 0w in
  let one = BoundedInterval64
    (BoundedSigned64 F 1099511627776w)
    (BoundedSigned64 F 1099511627776w) in
  let state = BoundedTaylor64 T one zeros6 one zeros6 zeros21 in
  bounded_taylor64_program_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one)
      [BoundedTaylor64Constant one; BoundedTaylor64Square] = SOME state ∧
  bounded_taylor64_program_eval radii (REPLICATE 6 one)
      (REPLICATE 6 one) [BoundedTaylor64Add] = NONE
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
