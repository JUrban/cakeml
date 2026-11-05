(*****************************************************************************
 * Concrete structural contract for the authenticated case-16594 cell-0
 * dispatcher trace.
 *
 * The semantic witnesses remain a separate proof obligation.  This theory
 * fixes the common per-step clock floor, proves the exact 167-code length,
 * and discharges the complete trace against compute_default_clock.  It also
 * checks that the chosen floor dominates every ordinary polynomial in the
 * authenticated source program and all fixed operation-family floors.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCell0TraceContract
Ancestors
  compute_boundedCase16594ObjectDispatchSemanticTrace
  compute_boundedCase16594ObjectDispatchCell0PayloadIdentity
  compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariant
  compute_boundedCase16594ObjectSpecializedDispatchStepInvariant
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_dispatch_common_floor_dominates_fixed:
  (4106:num) <= 524405 /\
  (8213:num) <= 524405 /\
  (16387:num) <= 524405 /\
  (262502:num) <= 524405
Proof
  simp []
QED

Theorem bounded_case16594_object_dispatch_common_floor_dominates_polynomials:
  EVERY
    (\source.
      case source of
      | BoundedAnalyticPolynomial program =>
          4105 + LENGTH program <= 524405
      | _ => T)
    bounded_case16594_program
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_runtime_cell0_codes_cv_length:
  bounded_case16594_object_cv_list_length
    bounded_case16594_runtime_cell0_codes_cv = 167
Proof
  rw
    [compute_boundedCase16594ObjectDispatchCell0PayloadIdentityTheory.bounded_case16594_runtime_cell0_codes_identity,
     compute_boundedCase16594DispatchRuntimePlanIdentityTheory.bounded_case16594_dispatch_codes_cv_def,
     compute_boundedCase16594DispatchRuntimePlanIdentityTheory.bounded_case16594_dispatch_code_cv_def,
     compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_cv_list_length_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_dispatch_cell0_default_clock_capacity:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 2 <
    compute_default_clock
Proof
  simp
    [bounded_case16594_runtime_cell0_codes_cv_length,
     computeTheory.compute_default_clock]
QED

Theorem bounded_case16594_object_dispatch_cell0_trace_eval_default_clock:
  bounded_case16594_object_dispatch_semantic_trace 524405
    bounded_case16594_runtime_cell0_center_boxes_cv
    bounded_case16594_runtime_cell0_outer_boxes_cv
    bounded_case16594_runtime_cell0_radii_cv
    semantic_radii weights semantic_center_boxes semantic_outer_boxes
    bounded_case16594_program bounded_case16594_prepared_program
    bounded_case16594_runtime_cell0_codes_cv
    bounded_case16594_runtime_cell0_sources_cv
    bounded_case16594_runtime_cell0_certificates_cv [] semantic_state
    final_runtime_state final_semantic_state ==>
  compute_eval compute_default_clock
    bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_program»
      [from_cv bounded_case16594_runtime_cell0_center_boxes_cv;
       from_cv bounded_case16594_runtime_cell0_outer_boxes_cv;
       from_cv bounded_case16594_runtime_cell0_radii_cv;
       from_cv bounded_case16594_runtime_cell0_codes_cv;
       from_cv bounded_case16594_runtime_cell0_sources_cv;
       from_cv bounded_case16594_runtime_cell0_certificates_cv;
       from_cv (bounded_object_q_cv_list [])])
    (refs:hol_refs) =
  (M_success (from_cv final_runtime_state),refs)
Proof
  metis_tac
    [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_semantic_trace_eval,
     bounded_case16594_object_dispatch_cell0_default_clock_capacity]
QED

val _ = export_theory ();
