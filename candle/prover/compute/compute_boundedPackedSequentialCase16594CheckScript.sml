(*****************************************************************************
 * Streaming complete checker for the external case16594 fixture.
 *
 * Parsing and numerical checking meet one cell at a time.  The checker does
 * not retain the 875 decoded cells and accepts only if the authenticated
 * header, every complete 31-certificate cell, the numerical verdicts, and
 * end-of-input all agree.
 *****************************************************************************)
Theory compute_boundedPackedSequentialCase16594Check
Ancestors
  compute_boundedPackedSequentialInput
  compute_boundedCase16594PreparedPlan
Libs
  bossLib preamble

Definition bounded_packed_case16594_result_accepts_def:
  bounded_packed_case16594_result_accepts
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    (domain ∧ bounded_signed64_strict_negative
      (bounded_interval64_upper value_bound))
End

Definition bounded_packed_chars_case16594_eval_cell_def:
  bounded_packed_chars_case16594_eval_cell
      ((box_environment,center_environment,radii),certificates) =
    case bounded_analytic64_program_eval radii center_environment
      box_environment bounded_case16594_prepared_program certificates of
    | NONE => F
    | SOME result => bounded_packed_case16594_result_accepts result
End

Definition bounded_packed_chars_case16594_check_cells_def:
  bounded_packed_chars_case16594_check_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_case16594_check_cells (SUC remaining) bytes count =
    case bounded_packed_chars_case16594_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        if bounded_packed_chars_case16594_eval_cell cell then
          bounded_packed_chars_case16594_check_cells remaining rest
            (SUC count)
        else NONE
End

Definition bounded_packed_chars_case16594_complete_check_def:
  bounded_packed_chars_case16594_complete_check bytes ⇔
    case bounded_packed_chars_case16594_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case16594_check_cells 875 rest 0 = SOME 875
End

Definition bounded_packed_chars_case16594_cell_status_def:
  bounded_packed_chars_case16594_cell_status
      ((box_environment,center_environment,radii),certificates) =
    case bounded_analytic64_program_eval radii center_environment
      box_environment bounded_case16594_prepared_program certificates of
    | NONE => 2
    | SOME (BoundedTaylor64 domain_valid center_value center_gradient
        value_bound gradient_bounds hessian) =>
      if ¬domain_valid then 3
      else if bounded_signed64_strict_negative
        (bounded_interval64_upper value_bound)
      then 4
      else 5
End

Definition bounded_packed_chars_case16594_first_status_def:
  bounded_packed_chars_case16594_first_status bytes =
    case bounded_packed_chars_case16594_header bytes of
    | NONE => 0
    | SOME rest =>
      case bounded_packed_chars_case16594_cell rest of
      | NONE => 1
      | SOME parsed =>
          bounded_packed_chars_case16594_cell_status (FST parsed)
End

Definition bounded_packed_sequential_case16594_complete_check_def:
  bounded_packed_sequential_case16594_complete_check (strlit bytes) ⇔
    bounded_packed_chars_case16594_complete_check bytes
End

Theorem bounded_packed_chars_case16594_eval_cell_success_well_formed:
  bounded_packed_chars_case16594_eval_cell
      ((box_environment,center_environment,radii),certificates) ⇒
  ∃result.
    bounded_analytic64_program_eval radii center_environment box_environment
      bounded_case16594_prepared_program certificates = SOME result ∧
    bounded_taylor64_well_formed result
Proof
  rw [bounded_packed_chars_case16594_eval_cell_def]
  >> every_case_tac >> fs []
  >> metis_tac
       [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some]
QED

Theorem bounded_packed_sequential_case16594_complete_check_truncated:
  ¬bounded_packed_sequential_case16594_complete_check «»
Proof
  simp [bounded_packed_sequential_case16594_complete_check_def,
        bounded_packed_chars_case16594_complete_check_def,
        bounded_packed_chars_case16594_header_def,
        bounded_packed_chars_prefix_def]
QED

Theorem bounded_packed_chars_case16594_first_status_truncated:
  bounded_packed_chars_case16594_first_status [] = 0
Proof
  EVAL_TAC
QED

val _ = export_theory ();
