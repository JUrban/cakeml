(*****************************************************************************
 * Semantic boundary for one accepted packed analytic cell.
 *
 * The byte parser supplies word intervals, but their endpoint ordering is a
 * separate fail-closed contract.  This theory keeps that requirement
 * explicit and turns valid decoded environments into their exact object-q
 * witnesses before applying the complete analytic-program refinement.
 *****************************************************************************)
Theory compute_boundedPackedAnalyticSoundBoundary
Ancestors
  compute_boundedPackedAnalyticCheck
  compute_boundedAnalyticObjectProgramRunRefinement
  compute_boundedAnalyticPlanCV
  compute_boundedAnalyticPreparedPlanRefinement
Libs
  bossLib preamble

Theorem bounded_interval64_valid_list_covers_own_object_q:
  !intervals.
    EVERY bounded_interval64_valid intervals ==>
    LIST_REL bounded_interval64_covers_object_q intervals
      (MAP bounded_interval64_object_q_cv intervals)
Proof
  Induct
  >> simp
       [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
QED

Theorem bounded_taylor_radius_pairs_length_six:
  LENGTH radii = 6 ==>
  ?weights. bounded_taylor_radius_pairs radii = SOME weights
Proof
  strip_tac
  >> fs [LENGTH_EQ_NUM_compute]
  >> simp
       [compute_boundedTaylorCompleteTheory.bounded_taylor_radius_pairs_def]
QED

Theorem bounded_packed_chars_analytic_eval_cell_refines_object_q:
  LIST_REL (bounded_analytic_instruction_refines 6)
    source_program prepared_program /\
  EVERY bounded_interval64_valid center_environment /\
  EVERY bounded_interval64_valid box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_packed_chars_analytic_eval_cell prepared_program
    ((box_environment,center_environment,radii),certificates) ==>
  ?word_result object_result.
    bounded_analytic64_program_eval radii center_environment box_environment
      prepared_program certificates = SOME word_result /\
    bounded_packed_analytic_result_accepts word_result /\
    bounded_object_q_analytic_run radii weights
      (MAP bounded_interval64_object_q_cv center_environment)
      (MAP bounded_interval64_object_q_cv box_environment)
      source_program prepared_program ([],certificates)
      ([object_result],[]) /\
    bounded_taylor64_covers_object_q word_result object_result
Proof
  strip_tac
  >> fs
       [compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_eval_cell_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_analytic64_program_eval radii center_environment
          box_environment prepared_program certificates = SOME word_result`
  >> mp_tac
       (Q.INST
         [`source_program` |-> `source_program`,
          `prepared_program` |-> `prepared_program`,
          `center_environment` |-> `center_environment`,
          `object_center_environment` |->
            `MAP bounded_interval64_object_q_cv center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |->
            `MAP bounded_interval64_object_q_cv box_environment`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `certificates` |-> `certificates`,
          `word_result` |-> `word_result`]
         compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_analytic64_program_eval_refines_object_q)
  >> impl_tac
  >- simp [bounded_interval64_valid_list_covers_own_object_q]
  >> metis_tac []
QED


Theorem bounded_packed_chars_analytic_validated_eval_cell_refines_object_q:
  LIST_REL (bounded_analytic_instruction_refines 6)
    source_program prepared_program /\
  bounded_packed_chars_analytic_validated_eval_cell prepared_program
    ((box_environment,center_environment,radii),certificates) ==>
  bounded_packed_analytic_int_geometry
    box_environment center_environment radii /\
  ?weights word_result object_result.
      bounded_taylor_radius_pairs radii = SOME weights /\
      bounded_analytic64_program_eval radii center_environment box_environment
        prepared_program certificates = SOME word_result /\
      bounded_packed_analytic_result_accepts word_result /\
      bounded_object_q_analytic_run radii weights
        (MAP bounded_interval64_object_q_cv center_environment)
        (MAP bounded_interval64_object_q_cv box_environment)
        source_program prepared_program ([],certificates)
        ([object_result],[]) /\
      bounded_taylor64_covers_object_q word_result object_result
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_validated_eval_cell_contract
  >> imp_res_tac
       compute_boundedPackedAnalyticCheckTheory.bounded_packed_analytic_geometry_ok_int
  >> imp_res_tac bounded_taylor_radius_pairs_length_six
  >> imp_res_tac bounded_packed_chars_analytic_eval_cell_refines_object_q
  >> metis_tac []
QED

Definition bounded_packed_analytic_object_cell_def:
  bounded_packed_analytic_object_cell source_program prepared_program
      ((box_environment,center_environment,radii),certificates) <=>
    bounded_packed_analytic_int_geometry
      box_environment center_environment radii /\
    ?weights word_result object_result.
        bounded_taylor_radius_pairs radii = SOME weights /\
        bounded_analytic64_program_eval radii center_environment box_environment
          prepared_program certificates = SOME word_result /\
        bounded_packed_analytic_result_accepts word_result /\
        bounded_object_q_analytic_run radii weights
          (MAP bounded_interval64_object_q_cv center_environment)
          (MAP bounded_interval64_object_q_cv box_environment)
          source_program prepared_program ([],certificates)
          ([object_result],[]) /\
        bounded_taylor64_covers_object_q word_result object_result
End

Definition bounded_packed_chars_analytic_object_cells_def:
  bounded_packed_chars_analytic_object_cells source_program prepared_program
      dimension certificate_count 0 bytes = (bytes = []) /\
  bounded_packed_chars_analytic_object_cells source_program prepared_program
      dimension certificate_count (SUC remaining) bytes =
    case bounded_packed_chars_analytic_cell
      dimension certificate_count bytes of
    | NONE => F
    | SOME (cell,rest) =>
        bounded_packed_analytic_object_cell
          source_program prepared_program cell /\
        bounded_packed_chars_analytic_object_cells
          source_program prepared_program dimension certificate_count
          remaining rest
End

Theorem bounded_packed_chars_analytic_validated_eval_cell_object:
  LIST_REL (bounded_analytic_instruction_refines 6)
      source_program prepared_program /\
  bounded_packed_chars_analytic_validated_eval_cell prepared_program cell ==>
  bounded_packed_analytic_object_cell source_program prepared_program cell
Proof
  PairCases_on `cell`
  >> simp [bounded_packed_analytic_object_cell_def]
  >> metis_tac
       [bounded_packed_chars_analytic_validated_eval_cell_refines_object_q]
QED

Theorem bounded_packed_chars_analytic_validated_check_cells_refines_object_q:
  !remaining bytes count result.
    LIST_REL (bounded_analytic_instruction_refines 6)
        source_program prepared_program /\
    bounded_packed_chars_analytic_validated_check_cells
      prepared_program dimension certificate_count remaining bytes count =
        SOME result ==>
    bounded_packed_chars_analytic_object_cells
      source_program prepared_program dimension certificate_count
      remaining bytes
Proof
  Induct
  >> simp
       [bounded_packed_chars_analytic_object_cells_def,
        compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_validated_check_cells_def]
  >> rpt gen_tac
  >> strip_tac
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [bounded_packed_chars_analytic_validated_eval_cell_object]
QED

Theorem bounded_packed_chars_analytic_validated_complete_refines_object_q:
  LIST_REL (bounded_analytic_instruction_refines 6)
      source_program prepared_program /\
  bounded_packed_chars_analytic_validated_complete_check
      prepared_program dimension cell_count certificate_count bytes ==>
  ?rest.
    bounded_packed_chars_analytic_header
      ((n2w cell_count):word64) ((n2w certificate_count):word64) bytes =
        SOME rest /\
    bounded_packed_chars_analytic_object_cells
      source_program prepared_program dimension certificate_count
      cell_count rest
Proof
  rw
    [compute_boundedPackedAnalyticCheckTheory.bounded_packed_chars_analytic_validated_complete_check_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [bounded_packed_chars_analytic_validated_check_cells_refines_object_q]
QED

Theorem bounded_analytic_source_plan_check_refines_object_q:
  bounded_analytic_source_plan_check source_cv metadata bytes ==>
  ?source_program prepared_program cell_count rest.
    bounded_analytic_program_of_cv source_cv = SOME source_program /\
    bounded_analytic_plan_metadata_of_cv metadata =
      SOME (BoundedAnalyticPlanMetadata 6 cell_count) /\
    bounded_analytic_compile_program 6 source_program =
      SOME prepared_program /\
    bounded_packed_chars_analytic_header
      ((n2w cell_count):word64)
      ((n2w (bounded_analytic64_certificate_count prepared_program)):word64)
      bytes = SOME rest /\
    bounded_packed_chars_analytic_object_cells
      source_program prepared_program 6
      (bounded_analytic64_certificate_count prepared_program)
      cell_count rest
Proof
  rw [compute_boundedAnalyticPlanCVTheory.bounded_analytic_source_plan_check_def,
      compute_boundedAnalyticPlanCVTheory.bounded_analytic_program_plan_check_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_compile_program_refines
  >> imp_res_tac
       bounded_packed_chars_analytic_validated_complete_refines_object_q
  >> metis_tac []
QED

val _ = export_theory ();
