(*****************************************************************************
 * Complete postfix-program refinement for object-q polynomial semantics.
 *
 * The one-step theorem is lifted through the actual executable program run.
 * This keeps the later analytic-instruction proof independent of expression
 * length and makes the singleton-result boundary explicit.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectPolyRunRefinement
Ancestors
  compute_boundedAnalyticObjectPolyStepRefinement
Libs
  bossLib preamble

Definition bounded_object_q_poly_run_def:
  bounded_object_q_poly_run radii weights center_environment box_environment
      [] stack = SOME stack /\
  bounded_object_q_poly_run radii weights center_environment box_environment
      (instruction::instructions) stack =
    case bounded_object_q_poly_step radii weights center_environment
      box_environment instruction stack of
    | NONE => NONE
    | SOME next =>
        bounded_object_q_poly_run radii weights center_environment
          box_environment instructions next
End

Theorem bounded_taylor64_poly_run_refines:
  !source_program prepared_program word_stack object_stack word_result.
    LIST_REL (bounded_analytic_poly_instruction_refines 6)
      source_program prepared_program /\
    bounded_taylor64_stack_covers_object_q word_stack object_stack /\
    LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
    LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_program_run radii center_environment box_environment
      prepared_program word_stack = SOME word_result ==>
    ?object_result.
      bounded_object_q_poly_run radii weights object_center_environment
        object_box_environment source_program object_stack =
          SOME object_result /\
      bounded_taylor64_stack_covers_object_q word_result object_result
Proof
  Induct_on `source_program`
  >- (Cases_on `prepared_program`
      >> simp [bounded_object_q_poly_run_def,
               compute_boundedTaylorProgramTheory.bounded_taylor64_program_run_def,
               LIST_REL_def])
  >> Cases_on `prepared_program`
  >- simp [LIST_REL_def]
  >> rpt gen_tac
  >> strip_tac
  >> rename1
       `LIST_REL (bounded_analytic_poly_instruction_refines 6)
          (source_instruction::source_rest)
          (prepared_instruction::prepared_rest)`
  >> fs [LIST_REL_def]
  >> Cases_on
       `bounded_taylor64_program_step radii center_environment
          box_environment prepared_instruction word_stack`
  >> fs [compute_boundedTaylorProgramTheory.bounded_taylor64_program_run_def]
  >> gvs []
  >> rename1
       `bounded_taylor64_program_step radii center_environment
          box_environment prepared_instruction word_stack = SOME word_next`
  >> mp_tac
       (Q.INST
         [`source` |-> `source_instruction`,
          `prepared` |-> `prepared_instruction`,
          `word_stack` |-> `word_stack`, `object_stack` |-> `object_stack`,
          `center_environment` |-> `center_environment`,
          `object_center_environment` |-> `object_center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |-> `object_box_environment`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `word_next` |-> `word_next`]
         bounded_taylor64_poly_step_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_next` strip_assume_tac)
  >> first_x_assum
       (qspecl_then
         [`prepared_rest`, `word_next`, `object_next`, `word_result`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac `object_result`
  >> asm_rewrite_tac [bounded_object_q_poly_run_def]
  >> simp []
QED

Theorem bounded_taylor64_poly_eval_refines:
  LIST_REL (bounded_analytic_poly_instruction_refines 6)
    source_program prepared_program /\
  LIST_REL bounded_interval64_covers_object_q
    center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
    box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_program_eval radii center_environment box_environment
    prepared_program = SOME word_result ==>
  ?object_result.
    bounded_object_q_poly_run radii weights object_center_environment
      object_box_environment source_program [] = SOME [object_result] /\
    bounded_taylor64_covers_object_q word_result object_result
Proof
  rw [compute_boundedTaylorProgramTheory.bounded_taylor64_program_eval_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_taylor64_program_run radii center_environment
          box_environment prepared_program [] = SOME [word_result]`
  >> mp_tac
       (Q.SPECL
         [`source_program`, `prepared_program`, `[]`, `[]`, `[word_result]`]
         (Q.INST
          [`center_environment` |-> `center_environment`,
          `object_center_environment` |-> `object_center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |-> `object_box_environment`,
          `radii` |-> `radii`, `weights` |-> `weights`]
          bounded_taylor64_poly_run_refines))
  >> impl_tac
  >- simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def]
  >> disch_then (qx_choose_then `object_stack` strip_assume_tac)
  >> Cases_on `object_stack`
  >> gvs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        LIST_REL_def]
  >> Cases_on `t`
  >> gvs [LIST_REL_def]
  >> metis_tac []
QED

val _ = export_theory ();
