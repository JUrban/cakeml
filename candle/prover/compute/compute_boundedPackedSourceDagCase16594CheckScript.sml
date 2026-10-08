(*****************************************************************************
 * Development complete checker using the exact source-DAG schedule.
 *
 * The external byte parser and final predicate are unchanged.  Only the
 * numerical evaluator differs from the sequential control.  The schedule is
 * computed from the pinned source and specialization roles, and every reuse
 * of a certificate-bearing node must present the identical typed
 * certificate.  This is DEVELOPMENT / NON-RELEASE until the general
 * sequential-equivalence/soundness theorem is complete.
 *****************************************************************************)
Theory compute_boundedPackedSourceDagCase16594Check
Ancestors
  compute_boundedPackedSequentialInput
  compute_boundedCase16594SourceDagEval
Libs
  bossLib preamble

Definition bounded_packed_source_dag_case16594_result_accepts_def:
  bounded_packed_source_dag_case16594_result_accepts
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    (domain ∧ bounded_signed64_strict_negative
      (bounded_interval64_upper value_bound))
End

Definition bounded_packed_chars_source_dag_case16594_eval_cell_def:
  bounded_packed_chars_source_dag_case16594_eval_cell
      ((box_environment,center_environment,radii),certificates) =
    case bounded_case16594_source_dag_eval_fast radii center_environment
      box_environment certificates of
    | NONE => F
    | SOME result =>
        bounded_packed_source_dag_case16594_result_accepts result
End

Definition bounded_packed_chars_source_dag_case16594_check_cells_def:
  bounded_packed_chars_source_dag_case16594_check_cells 0 bytes count =
      (if bytes = [] then SOME count else NONE) ∧
  bounded_packed_chars_source_dag_case16594_check_cells
      (SUC remaining) bytes count =
    case bounded_packed_chars_case16594_cell bytes of
    | NONE => NONE
    | SOME (cell,rest) =>
        if bounded_packed_chars_source_dag_case16594_eval_cell cell then
          bounded_packed_chars_source_dag_case16594_check_cells
            remaining rest (SUC count)
        else NONE
End

Definition bounded_packed_chars_source_dag_case16594_complete_check_def:
  bounded_packed_chars_source_dag_case16594_complete_check bytes ⇔
    case bounded_packed_chars_case16594_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_source_dag_case16594_check_cells
          875 rest 0 = SOME 875
End

Definition bounded_packed_source_dag_case16594_complete_check_def:
  bounded_packed_source_dag_case16594_complete_check (strlit bytes) ⇔
    bounded_packed_chars_source_dag_case16594_complete_check bytes
End

Theorem bounded_packed_source_dag_case16594_complete_check_truncated:
  ¬bounded_packed_source_dag_case16594_complete_check «»
Proof
  simp [bounded_packed_source_dag_case16594_complete_check_def,
        bounded_packed_chars_source_dag_case16594_complete_check_def,
        bounded_packed_chars_case16594_header_def,
        bounded_packed_chars_prefix_def]
QED

val _ = export_theory ();
