(*****************************************************************************
 * Program-parameterized streaming checker for packed analytic certificates.
 *
 * This is the reusable core below family-specific source correspondence.
 * Dimensions, record counts, cell counts, and the prepared analytic program
 * are explicit inputs.  The case-16594 specialization theorem at the end
 * makes the refactor checkable without changing the established executable.
 *****************************************************************************)
Theory compute_boundedPackedAnalyticCheck
Ancestors
  compute_boundedPackedSequentialInput
  compute_boundedCase16594PreparedPlan
  compute_boundedPackedSequentialCase16594Check
Libs
  bossLib preamble

Definition bounded_packed_chars_analytic_input_def:
  bounded_packed_chars_analytic_input dimension bytes =
    case bounded_packed_chars_positive_interval64_list dimension bytes of
    | NONE => NONE
    | SOME (box,rest1) =>
      case bounded_packed_chars_positive_interval64_list dimension rest1 of
      | NONE => NONE
      | SOME (center,rest2) =>
        case bounded_packed_chars_word64_list dimension rest2 of
        | NONE => NONE
        | SOME (radii,finish) => SOME ((box,center,radii),finish)
End

Definition bounded_packed_chars_analytic_cell_def:
  bounded_packed_chars_analytic_cell dimension certificate_count bytes =
    case bounded_packed_chars_analytic_input dimension bytes of
    | NONE => NONE
    | SOME (input,rest) =>
      case bounded_packed_chars_analytic64_certificate_list
        certificate_count rest of
      | NONE => NONE
      | SOME (certificates,finish) => SOME ((input,certificates),finish)
End

Definition bounded_packed_chars_analytic_header_def:
  bounded_packed_chars_analytic_header expected_cells expected_records bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"C";#"K";#"R";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,rest1) =>
        case bounded_packed_chars_word64_aux 4 rest1 of
        | NONE => NONE
        | SOME (records,finish) =>
          if cells = expected_cells /\ records = expected_records
          then SOME finish
          else NONE
End

Definition bounded_packed_analytic_result_accepts_def:
  bounded_packed_analytic_result_accepts
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    (domain /\ bounded_signed64_strict_negative
      (bounded_interval64_upper value_bound))
End

Definition bounded_packed_chars_analytic_eval_cell_def:
  bounded_packed_chars_analytic_eval_cell program
      ((box_environment,center_environment,radii),certificates) =
    case bounded_analytic64_program_eval radii center_environment
      box_environment program certificates of
    | NONE => F
    | SOME result => bounded_packed_analytic_result_accepts result
End

Definition bounded_packed_chars_analytic_check_cells_def:
  bounded_packed_chars_analytic_check_cells
      program dimension certificate_count 0 bytes count =
      (if bytes = [] then SOME count else NONE) /\
  bounded_packed_chars_analytic_check_cells
      program dimension certificate_count (SUC remaining) bytes count =
    case bounded_packed_chars_analytic_cell
      dimension certificate_count bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        if bounded_packed_chars_analytic_eval_cell program cell then
          bounded_packed_chars_analytic_check_cells
            program dimension certificate_count remaining rest (SUC count)
        else NONE
End

Definition bounded_packed_chars_analytic_complete_check_def:
  bounded_packed_chars_analytic_complete_check
      program dimension cell_count certificate_count bytes <=>
    cell_count < 4294967296 /\
    certificate_count < 4294967296 /\
    case bounded_packed_chars_analytic_header
      ((n2w cell_count):word64) ((n2w certificate_count):word64) bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_analytic_check_cells
          program dimension certificate_count cell_count rest 0 =
            SOME cell_count
End

(*****************************************************************************
 * Fail-closed production boundary.
 *
 * The legacy case-specific checker predates the exact object-q refinement
 * and remains below as a regression oracle.  New plan-driven calls use this
 * wrapper, which authenticates the six-dimensional Taylor shape and the
 * endpoint ordering needed by the semantic theorem before evaluation.
 *****************************************************************************)

Definition bounded_packed_analytic_input_valid_def:
  bounded_packed_analytic_input_valid
      (box_environment,center_environment,radii) <=>
    LENGTH box_environment = 6 /\
    LENGTH center_environment = 6 /\
    LENGTH radii = 6 /\
    EVERY bounded_interval64_valid box_environment /\
    EVERY bounded_interval64_valid center_environment
End

Definition bounded_packed_chars_analytic_validated_eval_cell_def:
  bounded_packed_chars_analytic_validated_eval_cell program
      ((box_environment,center_environment,radii),certificates) <=>
    bounded_packed_analytic_input_valid
      (box_environment,center_environment,radii) /\
    bounded_packed_chars_analytic_eval_cell program
      ((box_environment,center_environment,radii),certificates)
End

Definition bounded_packed_chars_analytic_validated_check_cells_def:
  bounded_packed_chars_analytic_validated_check_cells
      program dimension certificate_count 0 bytes count =
      (if bytes = [] then SOME count else NONE) /\
  bounded_packed_chars_analytic_validated_check_cells
      program dimension certificate_count (SUC remaining) bytes count =
    case bounded_packed_chars_analytic_cell
      dimension certificate_count bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        if bounded_packed_chars_analytic_validated_eval_cell program cell then
          bounded_packed_chars_analytic_validated_check_cells
            program dimension certificate_count remaining rest (SUC count)
        else NONE
End

Definition bounded_packed_chars_analytic_validated_complete_check_def:
  bounded_packed_chars_analytic_validated_complete_check
      program dimension cell_count certificate_count bytes <=>
    dimension = 6 /\
    cell_count < 4294967296 /\
    certificate_count < 4294967296 /\
    case bounded_packed_chars_analytic_header
      ((n2w cell_count):word64) ((n2w certificate_count):word64) bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_analytic_validated_check_cells
          program dimension certificate_count cell_count rest 0 =
            SOME cell_count
End

Theorem bounded_packed_chars_analytic_validated_eval_cell_contract:
  bounded_packed_chars_analytic_validated_eval_cell program
      ((box_environment,center_environment,radii),certificates) ==>
  LENGTH box_environment = 6 /\
  LENGTH center_environment = 6 /\
  LENGTH radii = 6 /\
  EVERY bounded_interval64_valid box_environment /\
  EVERY bounded_interval64_valid center_environment /\
  bounded_packed_chars_analytic_eval_cell program
      ((box_environment,center_environment,radii),certificates)
Proof
  simp [bounded_packed_chars_analytic_validated_eval_cell_def,
        bounded_packed_analytic_input_valid_def]
QED

Theorem bounded_packed_analytic_input_valid_rejects_invalid_box_interval:
  ~bounded_interval64_valid interval ==>
  ~bounded_packed_analytic_input_valid
    (interval::box_environment,center_environment,radii)
Proof
  simp [bounded_packed_analytic_input_valid_def]
QED

Theorem bounded_packed_analytic_input_valid_rejects_invalid_center_interval:
  ~bounded_interval64_valid interval ==>
  ~bounded_packed_analytic_input_valid
    (box_environment,interval::center_environment,radii)
Proof
  simp [bounded_packed_analytic_input_valid_def]
QED

Theorem bounded_packed_chars_analytic_validated_check_cells_imp:
  !remaining bytes count result.
    bounded_packed_chars_analytic_validated_check_cells
      program dimension certificate_count remaining bytes count =
        SOME result ==>
    bounded_packed_chars_analytic_check_cells
      program dimension certificate_count remaining bytes count = SOME result
Proof
  Induct
  >> simp [bounded_packed_chars_analytic_validated_check_cells_def,
           bounded_packed_chars_analytic_check_cells_def]
  >> rpt gen_tac
  >> TOP_CASE_TAC
  >> simp []
  >> PairCases_on `x`
  >> simp [bounded_packed_chars_analytic_validated_eval_cell_def]
QED

Theorem bounded_packed_chars_analytic_validated_complete_check_imp:
  bounded_packed_chars_analytic_validated_complete_check
      program dimension cell_count certificate_count bytes ==>
  bounded_packed_chars_analytic_complete_check
      program dimension cell_count certificate_count bytes
Proof
  rw [bounded_packed_chars_analytic_validated_complete_check_def,
      bounded_packed_chars_analytic_complete_check_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [bounded_packed_chars_analytic_validated_check_cells_imp]
QED

Theorem bounded_packed_chars_analytic_input_case16594:
  bounded_packed_chars_analytic_input 6 bytes =
    bounded_packed_chars_case16594_input bytes
Proof
  simp [bounded_packed_chars_analytic_input_def,
        bounded_packed_chars_case16594_input_def]
QED

Theorem bounded_packed_chars_analytic_cell_case16594:
  bounded_packed_chars_analytic_cell 6 31 bytes =
    bounded_packed_chars_case16594_cell bytes
Proof
  simp [bounded_packed_chars_analytic_cell_def,
        bounded_packed_chars_case16594_cell_def,
        bounded_packed_chars_analytic_input_case16594]
QED

Theorem bounded_packed_chars_analytic_header_case16594:
  bounded_packed_chars_analytic_header 875w 31w bytes =
    bounded_packed_chars_case16594_header bytes
Proof
  simp [bounded_packed_chars_analytic_header_def,
        bounded_packed_chars_case16594_header_def]
QED

Theorem bounded_packed_analytic_result_accepts_case16594:
  bounded_packed_analytic_result_accepts result =
    bounded_packed_case16594_result_accepts result
Proof
  Cases_on `result`
  >> simp [bounded_packed_analytic_result_accepts_def,
           bounded_packed_case16594_result_accepts_def]
QED

Theorem bounded_packed_chars_analytic_eval_cell_case16594:
  bounded_packed_chars_analytic_eval_cell
      bounded_case16594_prepared_program cell =
    bounded_packed_chars_case16594_eval_cell cell
Proof
  PairCases_on `cell`
  >> simp [bounded_packed_chars_analytic_eval_cell_def,
           bounded_packed_chars_case16594_eval_cell_def,
           bounded_packed_analytic_result_accepts_case16594]
QED

Theorem bounded_packed_chars_analytic_check_cells_case16594:
  !remaining bytes count.
    bounded_packed_chars_analytic_check_cells
        bounded_case16594_prepared_program 6 31 remaining bytes count =
      bounded_packed_chars_case16594_check_cells remaining bytes count
Proof
  Induct
  >> simp [bounded_packed_chars_analytic_check_cells_def,
           bounded_packed_chars_case16594_check_cells_def,
           bounded_packed_chars_analytic_cell_case16594,
           bounded_packed_chars_analytic_eval_cell_case16594]
  >> rpt gen_tac
  >> every_case_tac
  >> simp []
QED

Theorem bounded_packed_chars_analytic_complete_check_case16594:
  bounded_packed_chars_analytic_complete_check
      bounded_case16594_prepared_program 6 875 31 bytes <=>
    bounded_packed_chars_case16594_complete_check bytes
Proof
  simp [bounded_packed_chars_analytic_complete_check_def,
        bounded_packed_chars_case16594_complete_check_def,
        bounded_packed_chars_analytic_header_case16594,
        bounded_packed_chars_analytic_check_cells_case16594]
QED

Theorem bounded_packed_chars_analytic_eval_cell_success_well_formed:
  bounded_packed_chars_analytic_eval_cell program
      ((box_environment,center_environment,radii),certificates) ==>
  ?result.
    bounded_analytic64_program_eval radii center_environment box_environment
      program certificates = SOME result /\
    bounded_taylor64_well_formed result
Proof
  rw [bounded_packed_chars_analytic_eval_cell_def]
  >> every_case_tac >> fs []
  >> metis_tac
       [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_some]
QED

val _ = export_theory ();
