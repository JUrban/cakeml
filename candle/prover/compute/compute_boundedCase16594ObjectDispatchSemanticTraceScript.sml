(*****************************************************************************
 * Joint evaluator/semantic trace for the explicit-radius object dispatcher.
 *
 * The instruction-family proofs supply one joint step.  This theory performs
 * the list induction once: it projects the exact evaluator trace, the exact
 * object-q analytic run, the final stack invariant, and the structural clock
 * bound.  Certificate details remain local to the supplying step theorem.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchSemanticTrace
Ancestors
  compute_boundedCase16594ObjectDispatchProgramTraceEval
  compute_boundedCase16594ObjectPolyStackInvariant
  compute_boundedAnalyticProgramCV
  compute_boundedAnalyticObjectProgramRunRefinement
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_dispatch_semantic_trace_def:
  (bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      [] [] runtime_codes runtime_sources runtime_certificates runtime_stack
      semantic_state final_runtime_state final_semantic_state <=>
    runtime_codes = Num 0 /\
    runtime_sources = Num 0 /\
    final_runtime_state =
      Pair (Num 1) (Pair (bounded_object_q_cv_list runtime_stack)
        runtime_certificates) /\
    final_semantic_state = semantic_state /\
    bounded_object_q_taylor_stack_runtime_refines runtime_stack
      (FST semantic_state)) /\
  (bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      [] (_::_) runtime_codes runtime_sources runtime_certificates
      runtime_stack semantic_state final_runtime_state final_semantic_state
      <=> F) /\
  (bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      (_::_) [] runtime_codes runtime_sources runtime_certificates
      runtime_stack semantic_state final_runtime_state final_semantic_state
      <=> F) /\
  (bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      (source::source_rest) (prepared::prepared_rest)
      runtime_codes runtime_sources runtime_certificates runtime_stack
      semantic_state final_runtime_state final_semantic_state <=>
    ?runtime_code runtime_code_rest runtime_source runtime_source_rest
       next_runtime_certificates next_runtime_stack next_semantic_state.
      runtime_codes = Pair runtime_code runtime_code_rest /\
      runtime_sources = Pair runtime_source runtime_source_rest /\
      bounded_analytic_instruction_of_cv runtime_source = SOME source /\
      bounded_analytic_instruction_refines 6 source prepared /\
      bounded_case16594_object_dispatch_step_eval_above step_floor
        runtime_center_boxes runtime_outer_boxes runtime_radii runtime_code
        runtime_source runtime_certificates
        (bounded_object_q_cv_list runtime_stack)
        (bounded_object_q_cv_list next_runtime_stack)
        next_runtime_certificates /\
      bounded_object_q_analytic_step semantic_radii weights
        semantic_center_boxes semantic_outer_boxes source prepared
        semantic_state next_semantic_state /\
      bounded_object_q_taylor_stack_runtime_refines runtime_stack
        (FST semantic_state) /\
      bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
        (FST next_semantic_state) /\
      bounded_case16594_object_dispatch_semantic_trace step_floor
        runtime_center_boxes runtime_outer_boxes runtime_radii
        semantic_radii weights semantic_center_boxes semantic_outer_boxes
        source_rest prepared_rest runtime_code_rest runtime_source_rest
        next_runtime_certificates next_runtime_stack next_semantic_state
        final_runtime_state final_semantic_state)
End

Theorem bounded_case16594_object_dispatch_step_eval_above_weaken:
  bounded_case16594_object_dispatch_step_eval_above lower
    center_boxes outer_boxes radii code source certificates stack
    next_stack next_certificates /\
  lower <= upper ==>
  bounded_case16594_object_dispatch_step_eval_above upper
    center_boxes outer_boxes radii code source certificates stack
    next_stack next_certificates
Proof
  rw
    [compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_step_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_semantic_trace_projects_eval:
  !source_program prepared_program runtime_codes runtime_sources
     runtime_certificates runtime_stack semantic_state final_runtime_state
     final_semantic_state.
    bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      source_program prepared_program runtime_codes runtime_sources
      runtime_certificates runtime_stack semantic_state final_runtime_state
      final_semantic_state ==>
    bounded_case16594_object_dispatch_program_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii runtime_codes
      runtime_sources runtime_certificates
      (bounded_object_q_cv_list runtime_stack) final_runtime_state
Proof
  Induct_on `source_program`
  >- (Cases_on `prepared_program`
      >> simp
        [bounded_case16594_object_dispatch_semantic_trace_def,
         compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_trace_def])
  >> Cases_on `prepared_program`
  >- simp [bounded_case16594_object_dispatch_semantic_trace_def]
  >> rpt gen_tac
  >> rw [bounded_case16594_object_dispatch_semantic_trace_def]
  >> simp
    [compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_trace_def]
  >> qexists_tac `bounded_object_q_cv_list next_runtime_stack`
  >> qexists_tac `next_runtime_certificates`
  >> asm_rewrite_tac []
  >> first_x_assum match_mp_tac
  >> qexists_tac `t`
  >> qexists_tac `next_semantic_state`
  >> qexists_tac `final_semantic_state`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_dispatch_semantic_trace_projects_run:
  !source_program prepared_program runtime_codes runtime_sources
     runtime_certificates runtime_stack semantic_state final_runtime_state
     final_semantic_state.
    bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      source_program prepared_program runtime_codes runtime_sources
      runtime_certificates runtime_stack semantic_state final_runtime_state
      final_semantic_state ==>
    bounded_object_q_analytic_run semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source_program
      prepared_program semantic_state final_semantic_state
Proof
  Induct_on `source_program`
  >- (Cases_on `prepared_program`
      >> simp
        [bounded_case16594_object_dispatch_semantic_trace_def,
         compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def])
  >> Cases_on `prepared_program`
  >- simp [bounded_case16594_object_dispatch_semantic_trace_def]
  >> rpt gen_tac
  >> rw [bounded_case16594_object_dispatch_semantic_trace_def]
  >> simp
    [compute_boundedAnalyticObjectProgramRunRefinementTheory.bounded_object_q_analytic_run_def]
  >> qexists_tac `next_semantic_state`
  >> asm_rewrite_tac []
  >> first_x_assum match_mp_tac
  >> qexists_tac `runtime_code_rest`
  >> qexists_tac `runtime_source_rest`
  >> qexists_tac `next_runtime_certificates`
  >> qexists_tac `next_runtime_stack`
  >> qexists_tac `final_runtime_state`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_dispatch_semantic_trace_final_stack:
  !source_program prepared_program runtime_codes runtime_sources
     runtime_certificates runtime_stack semantic_state final_runtime_state
     final_semantic_state.
    bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      source_program prepared_program runtime_codes runtime_sources
      runtime_certificates runtime_stack semantic_state final_runtime_state
      final_semantic_state ==>
    ?final_runtime_stack final_runtime_certificates.
      final_runtime_state =
        Pair (Num 1)
          (Pair (bounded_object_q_cv_list final_runtime_stack)
            final_runtime_certificates) /\
      bounded_object_q_taylor_stack_runtime_refines final_runtime_stack
        (FST final_semantic_state)
Proof
  Induct_on `source_program`
  >- (Cases_on `prepared_program`
      >> simp [bounded_case16594_object_dispatch_semantic_trace_def]
      >> metis_tac [])
  >> Cases_on `prepared_program`
  >- simp [bounded_case16594_object_dispatch_semantic_trace_def]
  >> rpt gen_tac
  >> rw [bounded_case16594_object_dispatch_semantic_trace_def]
  >> first_x_assum match_mp_tac
  >> qexists_tac `t`
  >> qexists_tac `runtime_code_rest`
  >> qexists_tac `runtime_source_rest`
  >> qexists_tac `next_runtime_certificates`
  >> qexists_tac `next_runtime_stack`
  >> qexists_tac `next_semantic_state`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_dispatch_semantic_trace_eval:
  bounded_case16594_object_dispatch_semantic_trace step_floor
    runtime_center_boxes runtime_outer_boxes runtime_radii
    semantic_radii weights semantic_center_boxes semantic_outer_boxes
    source_program prepared_program runtime_codes runtime_sources
    runtime_certificates runtime_stack semantic_state final_runtime_state
    final_semantic_state /\
  step_floor +
      2 * bounded_case16594_object_cv_list_length runtime_codes + 2 < clock
  ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_program»
      [from_cv runtime_center_boxes;from_cv runtime_outer_boxes;
       from_cv runtime_radii;from_cv runtime_codes;from_cv runtime_sources;
       from_cv runtime_certificates;
       from_cv (bounded_object_q_cv_list runtime_stack)])
    (refs:hol_refs) =
  (M_success (from_cv final_runtime_state),refs)
Proof
  metis_tac
    [bounded_case16594_object_dispatch_semantic_trace_projects_eval,
     compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_dispatch_program_trace_sound]
QED

val _ = export_theory ();
