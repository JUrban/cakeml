(*****************************************************************************
 * Complete analytic-program refinement through exact object-q states.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectProgramRunRefinement
Ancestors
  compute_boundedAnalyticObjectCompleteDispatcherRefinement
Libs
  bossLib preamble

Definition bounded_object_q_analytic_run_def:
  bounded_object_q_analytic_run radii weights object_center_environment
      object_box_environment [] [] object_state object_result =
        (object_result = object_state) /\
  bounded_object_q_analytic_run radii weights object_center_environment
      object_box_environment [] (_::_) object_state object_result = F /\
  bounded_object_q_analytic_run radii weights object_center_environment
      object_box_environment (_::_) [] object_state object_result = F /\
  bounded_object_q_analytic_run radii weights object_center_environment
      object_box_environment (source::source_rest)
      (prepared::prepared_rest) object_state object_result =
    ?object_next.
      bounded_object_q_analytic_step radii weights
        object_center_environment object_box_environment source prepared
        object_state object_next /\
      bounded_object_q_analytic_run radii weights
        object_center_environment object_box_environment source_rest
        prepared_rest object_next object_result
End

Theorem bounded_analytic64_program_run_refines_object_q:
  !source_program prepared_program word_state object_state word_result.
    LIST_REL (bounded_analytic_instruction_refines 6)
      source_program prepared_program /\
    bounded_analytic64_state_covers_object_q word_state object_state /\
    LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
    LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_analytic64_program_run radii center_environment box_environment
      prepared_program word_state = SOME word_result ==>
    ?object_result.
      bounded_object_q_analytic_run radii weights object_center_environment
        object_box_environment source_program prepared_program object_state
        object_result /\
      bounded_analytic64_state_covers_object_q word_result object_result
Proof
  Induct_on `source_program`
  >- (Cases_on `prepared_program`
      >> simp [bounded_object_q_analytic_run_def,
               compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def,
               LIST_REL_def])
  >> Cases_on `prepared_program`
  >- simp [LIST_REL_def]
  >> rpt gen_tac
  >> strip_tac
  >> rename1
       `LIST_REL (bounded_analytic_instruction_refines 6)
          (source_instruction::source_rest)
          (prepared_instruction::prepared_rest)`
  >> fs [LIST_REL_def]
  >> Cases_on
       `bounded_analytic64_program_step radii center_environment
          box_environment prepared_instruction word_state`
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_run_def]
  >> gvs []
  >> rename1
       `bounded_analytic64_program_step radii center_environment
          box_environment prepared_instruction word_state = SOME word_next`
  >> mp_tac
       (Q.INST
         [`source` |-> `source_instruction`,
          `prepared` |-> `prepared_instruction`,
          `word_state` |-> `word_state`, `object_state` |-> `object_state`,
          `center_environment` |-> `center_environment`,
          `object_center_environment` |-> `object_center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |-> `object_box_environment`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `word_next` |-> `word_next`]
         compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_analytic64_complete_dispatch_refines_object_q)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_next` strip_assume_tac)
  >> first_x_assum
       (qspecl_then
         [`prepared_rest`, `word_next`, `object_next`, `word_result`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac `object_result`
  >> conj_tac
  >- (rw [bounded_object_q_analytic_run_def]
      >> qexists_tac `object_next`
      >> simp [])
  >> simp []
QED

Theorem bounded_analytic64_program_eval_refines_object_q:
  LIST_REL (bounded_analytic_instruction_refines 6)
    source_program prepared_program /\
  LIST_REL bounded_interval64_covers_object_q
    center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
    box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_eval radii center_environment box_environment
    prepared_program certificates = SOME word_result ==>
  ?object_result.
    bounded_object_q_analytic_run radii weights object_center_environment
      object_box_environment source_program prepared_program
      ([],certificates) ([object_result],[]) /\
    bounded_taylor64_covers_object_q word_result object_result
Proof
  rw [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_eval_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_analytic64_program_run radii center_environment
          box_environment prepared_program ([],certificates) =
            SOME ([word_result],[])`
  >> mp_tac
       (Q.SPECL
         [`source_program`, `prepared_program`, `([],certificates)`,
          `([],certificates)`, `([word_result],[])`]
         (Q.INST
          [`center_environment` |-> `center_environment`,
           `object_center_environment` |-> `object_center_environment`,
           `box_environment` |-> `box_environment`,
           `object_box_environment` |-> `object_box_environment`,
           `radii` |-> `radii`, `weights` |-> `weights`]
          bounded_analytic64_program_run_refines_object_q))
  >> impl_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def]
  >> disch_then (qx_choose_then `object_state` strip_assume_tac)
  >> PairCases_on `object_state`
  >> gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        LIST_REL_def]
  >> metis_tac []
QED

val _ = export_theory ();
