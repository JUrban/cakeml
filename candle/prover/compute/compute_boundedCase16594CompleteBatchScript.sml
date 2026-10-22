(*****************************************************************************
 * Complete checked-word case16594 certificate batch.
 *
 * The source-authenticated 167-instruction program, prepared box inputs, and
 * decompressed typed scalar certificates meet only at this boundary.  A cell
 * is accepted exactly when total program execution consumes its certificate
 * stream, produces one well-formed Taylor result with a valid domain, and the
 * upper endpoint of the completed bound is strictly negative.
 *****************************************************************************)
Theory compute_boundedCase16594CompleteBatch
Ancestors
  compute_boundedCase16594PreparedPlan
  compute_boundedCase16594PreparedInput
  compute_boundedCase16594PreparedCertificates
Libs
  bossLib preamble wordsLib

Definition bounded_case16594_certificate_arity_def:
  bounded_case16594_certificate_arity [] = 0 ∧
  bounded_case16594_certificate_arity (instruction::instructions) =
    (case instruction of
     | BoundedAnalytic64Sqrt => 1
     | BoundedAnalytic64Inverse => 1
     | BoundedAnalytic64Atan => 1
     | _ => 0) +
    bounded_case16594_certificate_arity instructions
End

Definition bounded_case16594_result_accepts_def:
  bounded_case16594_result_accepts
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    (domain ∧ bounded_signed64_strict_negative
      (bounded_interval64_upper value_bound))
End

Definition bounded_case16594_eval_cell_def:
  bounded_case16594_eval_cell input certificates =
    case input of
    | BoundedCase16594PreparedInput center_environment box_environment
        radii center_sqrt box_sqrt =>
      case bounded_analytic64_program_eval radii center_environment
        box_environment bounded_case16594_prepared_program certificates of
      | NONE => F
      | SOME result => bounded_case16594_result_accepts result
End

Definition bounded_case16594_eval_cells_def:
  bounded_case16594_eval_cells [] [] count = SOME count ∧
  bounded_case16594_eval_cells (input::inputs)
      (certificates::certificate_cells) count =
    (if bounded_case16594_eval_cell input certificates then
      bounded_case16594_eval_cells inputs certificate_cells (SUC count)
    else NONE) ∧
  bounded_case16594_eval_cells _ _ count = NONE
End

Definition bounded_case16594_complete_batch_def:
  bounded_case16594_complete_batch =
    bounded_case16594_eval_cells bounded_case16594_prepared_inputs
      bounded_case16594_prepared_certificates 0
End

Definition bounded_case16594_complete_batch_ok_def:
  bounded_case16594_complete_batch_ok ⇔
    bounded_case16594_prepared_inputs_ok ∧
    bounded_case16594_prepared_certificates_ok ∧
    bounded_case16594_complete_batch = SOME 875
End

Theorem bounded_case16594_prepared_program_certificate_arity:
  bounded_case16594_certificate_arity
    bounded_case16594_prepared_program = 31
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_case16594_eval_cell_success_well_formed:
  bounded_analytic64_program_eval radii center_environment box_environment
    bounded_case16594_prepared_program certificates = SOME result ⇒
  bounded_taylor64_well_formed result
Proof
  metis_tac
    [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some]
QED

val _ = export_theory ();
