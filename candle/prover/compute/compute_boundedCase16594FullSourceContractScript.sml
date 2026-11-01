(*****************************************************************************
 * Complete exact-source contract for every accepted case-16594 packed cell.
 *
 * The generic plan checker already refines each validated word cell to an
 * exact object-q source execution.  This theory preserves that source
 * witness while exposing the exact five-payload acceptance contract needed
 * by the ordinary Candle entry.  It is a batch theorem, not a closed-data
 * evaluation and not a replacement for the still-required full-source
 * compute_eval refinement.
 *****************************************************************************)
Theory compute_boundedCase16594FullSourceContract
Ancestors
  compute_boundedPackedAnalyticSoundBoundary
  compute_boundedPackedObjectSourceContractRefinement
  compute_boundedAnalyticPlanCV
Libs
  bossLib preamble

Definition bounded_case16594_packed_source_cell_contract_def:
  bounded_case16594_packed_source_cell_contract
      ((box_environment,center_environment,radii),certificates) <=>
    ?weights word_result object_domain center_value center_gradient
     gradient_bounds hessian.
      bounded_taylor_radius_pairs radii = SOME weights /\
      bounded_analytic64_program_eval radii center_environment
        box_environment bounded_case16594_prepared_program certificates =
          SOME word_result /\
      bounded_taylor64_covers_object_q word_result
        (BoundedObjectQTaylor object_domain center_value center_gradient
          (bounded_object_q_taylor_value_complete_cv center_value
            (bounded_object_q_taylor_error_cv radii center_gradient
              weights hessian))
          gradient_bounds hessian) /\
      bounded_packed_object_source_accept6
        (MAP bounded_word64_object_q_cv radii) center_value
        center_gradient hessian
End

Theorem bounded_case16594_packed_object_cell_source_contract:
  bounded_packed_analytic_object_cell bounded_case16594_program
      bounded_case16594_prepared_program cell ==>
  bounded_case16594_packed_source_cell_contract cell
Proof
  PairCases_on `cell`
  >> simp [bounded_case16594_packed_source_cell_contract_def]
  >> metis_tac
       [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_case16594_packed_cell_source_accept6]
QED

Definition bounded_case16594_packed_source_cells_contract_def:
  bounded_case16594_packed_source_cells_contract 0 bytes = (bytes = []) /\
  bounded_case16594_packed_source_cells_contract (SUC remaining) bytes =
    case bounded_packed_chars_analytic_cell 6 31 bytes of
    | NONE => F
    | SOME (cell,rest) =>
        bounded_case16594_packed_source_cell_contract cell /\
        bounded_case16594_packed_source_cells_contract remaining rest
End

Theorem bounded_case16594_packed_object_cells_source_contract:
  !remaining bytes.
    bounded_packed_chars_analytic_object_cells bounded_case16594_program
      bounded_case16594_prepared_program 6 31 remaining bytes ==>
    bounded_case16594_packed_source_cells_contract remaining bytes
Proof
  Induct
  >> simp
       [bounded_case16594_packed_source_cells_contract_def,
        compute_boundedPackedAnalyticSoundBoundaryTheory.bounded_packed_chars_analytic_object_cells_def]
  >> rpt gen_tac
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_case16594_packed_object_cell_source_contract]
QED

Theorem bounded_case16594_validated_complete_source_contract:
  bounded_packed_chars_analytic_validated_complete_check
      bounded_case16594_prepared_program 6 875 31 bytes ==>
  ?rest.
    bounded_packed_chars_analytic_header 875w 31w bytes = SOME rest /\
    bounded_case16594_packed_source_cells_contract 875 rest
Proof
  strip_tac
  >> `LIST_REL (bounded_analytic_instruction_refines 6)
        bounded_case16594_program bounded_case16594_prepared_program` by
       metis_tac
         [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_compile_program_refines,
          compute_boundedAnalyticPreparedPlanTheory.bounded_analytic_compile_program_case16594]
  >> imp_res_tac
       compute_boundedPackedAnalyticSoundBoundaryTheory.bounded_packed_chars_analytic_validated_complete_refines_object_q
  >> metis_tac [bounded_case16594_packed_object_cells_source_contract]
QED

Theorem bounded_case16594_source_plan_full_source_contract:
  bounded_analytic_source_plan_check bounded_case16594_source_program_cv
      bounded_case16594_plan_metadata_cv bytes ==>
  ?rest.
    bounded_packed_chars_analytic_header 875w 31w bytes = SOME rest /\
    bounded_case16594_packed_source_cells_contract 875 rest
Proof
  rw
    [compute_boundedAnalyticPlanCVTheory.bounded_analytic_source_plan_check_case16594_validated]
  >> metis_tac [bounded_case16594_validated_complete_source_contract]
QED

val _ = export_theory ();
