(*****************************************************************************
 * Composition for the joint evaluator/semantic trace.
 *
 * A prefix trace ends in the cv-list terminator Num 0.  This theory replaces
 * that terminator with a second authenticated trace, allowing ordinary
 * stretches and the six specialized delta positions to be proved separately
 * and then joined without replaying earlier instructions.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchSemanticTraceAppend
Ancestors
  compute_boundedCase16594ObjectDispatchSemanticTrace
  compute_boundedCase16594ObjectDeltaProductRefinementBridge
Libs
  bossLib preamble

Definition bounded_case16594_trace_cv_list_append_def:
  bounded_case16594_trace_cv_list_append (Num nil) right = right /\
  bounded_case16594_trace_cv_list_append (Pair item items) right =
    Pair item (bounded_case16594_trace_cv_list_append items right)
End

Theorem bounded_case16594_object_dispatch_semantic_trace_append:
  !source_left prepared_left runtime_codes_left runtime_sources_left
   runtime_certificates runtime_stack semantic_state middle_runtime_stack
   middle_runtime_certificates middle_semantic_state source_right
   prepared_right runtime_codes_right runtime_sources_right
   final_runtime_state final_semantic_state.
    bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      source_left prepared_left runtime_codes_left runtime_sources_left
      runtime_certificates runtime_stack semantic_state
      (Pair (Num 1)
        (Pair (bounded_object_q_cv_list middle_runtime_stack)
          middle_runtime_certificates))
      middle_semantic_state /\
    bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      source_right prepared_right runtime_codes_right runtime_sources_right
      middle_runtime_certificates middle_runtime_stack middle_semantic_state
      final_runtime_state final_semantic_state
    ==>
    bounded_case16594_object_dispatch_semantic_trace step_floor
      runtime_center_boxes runtime_outer_boxes runtime_radii
      semantic_radii weights semantic_center_boxes semantic_outer_boxes
      (source_left ++ source_right) (prepared_left ++ prepared_right)
      (bounded_case16594_trace_cv_list_append
        runtime_codes_left runtime_codes_right)
      (bounded_case16594_trace_cv_list_append
        runtime_sources_left runtime_sources_right)
      runtime_certificates runtime_stack semantic_state
      final_runtime_state final_semantic_state
Proof
  Induct_on `source_left`
  >- (Cases_on `prepared_left`
      >> simp
           [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
            bounded_case16594_trace_cv_list_append_def]
      >> rpt strip_tac
      >> `middle_runtime_stack = runtime_stack` by
           (irule
              compute_boundedCase16594ObjectDeltaProductRefinementBridgeTheory.bounded_case16594_object_q_cv_list_injective
            >> asm_rewrite_tac [])
      >> gvs [])
  >> Cases_on `prepared_left`
  >- simp
       [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def]
  >> rpt gen_tac
  >> rw
       [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_def,
        bounded_case16594_trace_cv_list_append_def]
  >> qexists_tac `runtime_code`
  >> qexists_tac
       `bounded_case16594_trace_cv_list_append runtime_code_rest
          runtime_codes_right`
  >> qexists_tac `runtime_source`
  >> qexists_tac
       `bounded_case16594_trace_cv_list_append runtime_source_rest
          runtime_sources_right`
  >> qexists_tac `next_runtime_certificates`
  >> qexists_tac `next_runtime_stack`
  >> qexists_tac `next_semantic_state`
  >> asm_rewrite_tac []
  >> qpat_x_assum
       `!prepared_left runtime_codes_left runtime_sources_left
          runtime_certificates runtime_stack semantic_state
          middle_runtime_stack middle_runtime_certificates
          middle_semantic_state source_right prepared_right
          runtime_codes_right runtime_sources_right final_runtime_state
          final_semantic_state. _`
       (mp_tac o Q.SPECL
         [`t`, `runtime_code_rest`, `runtime_source_rest`,
          `next_runtime_certificates`, `next_runtime_stack`,
          `next_semantic_state`, `middle_runtime_stack`,
          `middle_runtime_certificates`, `middle_semantic_state`,
          `source_right`, `prepared_right`, `runtime_codes_right`,
          `runtime_sources_right`, `final_runtime_state`,
          `final_semantic_state`])
  >> impl_tac
  >- asm_rewrite_tac []
  >> simp [bounded_case16594_trace_cv_list_append_def]
QED

val _ = export_theory ();
