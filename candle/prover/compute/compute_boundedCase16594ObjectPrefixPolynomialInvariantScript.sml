(*****************************************************************************
 * Shared production-dispatch invariant and semantic traces for the small
 * polynomial instructions surrounding the first genuine pi/2 and sqrt.
 *
 * This keeps the expensive source-0 computation separate while giving every
 * following constant-only polynomial the same authenticated runtime bridge.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPrefixPolynomialInvariant
Ancestors
  compute_boundedCase16594ObjectPiHalfInvariant
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_source1_result_def:
  bounded_case16594_object_source1_result =
    bounded_object_q_taylor_constant 1 0 0
End

Definition bounded_case16594_object_source2_result_def:
  bounded_case16594_object_source2_result =
    bounded_object_q_taylor_constant 3 0 0
End

Definition bounded_case16594_object_source4_result_def:
  bounded_case16594_object_source4_result =
    bounded_object_q_taylor_constant 1 0 2
End

Definition bounded_case16594_object_source5_result_def:
  bounded_case16594_object_source5_result =
    bounded_object_q_taylor_add
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      (bounded_object_q_taylor_constant 1 0 0)
      (bounded_object_q_taylor_neg
        bounded_case16594_object_cell0_word_radii
        bounded_case16594_object_cell0_weights
        (bounded_object_q_taylor_mul
          bounded_case16594_object_cell0_word_radii
          bounded_case16594_object_cell0_weights
          (bounded_object_q_taylor_constant 1 0 2)
          (bounded_object_q_taylor_constant 1 0 2)))
End

Theorem bounded_case16594_object_source1_semantic_trace:
  bounded_object_q_poly_run
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      center_boxes outer_boxes
      bounded_case16594_object_source1_poly_program [] =
    SOME [bounded_case16594_object_source1_result]
Proof
  simp
    [compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_source1_poly_program_def,
     bounded_case16594_object_source1_result_def,
     compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
QED

Theorem bounded_case16594_object_source2_semantic_trace:
  bounded_object_q_poly_run
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      center_boxes outer_boxes
      bounded_case16594_object_source2_poly_program [] =
    SOME [bounded_case16594_object_source2_result]
Proof
  simp
    [compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_source2_poly_program_def,
     bounded_case16594_object_source2_result_def,
     compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
QED

Theorem bounded_case16594_object_source4_semantic_trace:
  bounded_object_q_poly_run
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      center_boxes outer_boxes
      bounded_case16594_object_source4_poly_program [] =
    SOME [bounded_case16594_object_source4_result]
Proof
  simp
    [compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_source4_poly_program_def,
     bounded_case16594_object_source4_result_def,
     compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
QED

Theorem bounded_case16594_object_source5_semantic_trace:
  bounded_object_q_poly_run
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      center_boxes outer_boxes
      bounded_case16594_object_source5_poly_program [] =
    SOME [bounded_case16594_object_source5_result]
Proof
  simp
    [compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_source5_poly_program_def,
     bounded_case16594_object_source5_result_def,
     compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
QED

Theorem bounded_case16594_object_cell0_dispatch_poly_eval_runtime_refines:
  bounded_object_q_taylor_stack_runtime_refines
      runtime_stack semantic_stack /\
  bounded_analytic_instruction_of_cv runtime_source =
      SOME (BoundedAnalyticPolynomial semantic_program) /\
  bounded_object_q_poly_run
      bounded_case16594_object_cell0_word_radii
      bounded_case16594_object_cell0_weights
      bounded_case16594_object_cell0_center_boxes
      bounded_case16594_object_cell0_outer_boxes semantic_program [] =
      SOME [semantic_result] /\
  4105 + LENGTH semantic_program < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);from_cv runtime_source;from_cv certificates;
         from_cv (bounded_object_q_cv_list runtime_stack)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list (runtime_result::runtime_stack))
            certificates))),refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (semantic_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`, `refs` |-> `refs`,
          `runtime_radii` |->
            `bounded_case16594_object_cell0_runtime_radii`,
          `semantic_radii` |->
            `bounded_case16594_object_cell0_word_radii`,
          `weights` |-> `bounded_case16594_object_cell0_weights`,
          `runtime_center_boxes` |->
            `bounded_case16594_object_cell0_center_boxes`,
          `runtime_outer_boxes` |->
            `bounded_case16594_object_cell0_outer_boxes`,
          `semantic_center_boxes` |->
            `bounded_case16594_object_cell0_center_boxes`,
          `semantic_outer_boxes` |->
            `bounded_case16594_object_cell0_outer_boxes`,
          `runtime_stack` |-> `runtime_stack`,
          `semantic_stack` |-> `semantic_stack`,
          `runtime_source` |-> `runtime_source`,
          `semantic_program` |-> `semantic_program`,
          `semantic_result` |-> `semantic_result`,
          `certificates` |-> `certificates`]
         compute_boundedCase16594ObjectOrdinaryPolyInvariantTheory.bounded_case16594_object_ordinary_poly_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> simp
           [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encoded,
            compute_boundedCase16594ObjectFirstPolyRunBridgeTheory.bounded_case16594_object_source0_runtime_radii_length,
            compute_boundedCase16594ObjectFirstPolySemanticTheory.bounded_case16594_object_cell0_radius_pairs,
            compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_equivalent,
            compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_center_boxes_length,
            compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_outer_boxes_length,
            compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_center_boxes_equivalent,
            compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_outer_boxes_equivalent,
            compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_center_boxes_valid,
            compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_outer_boxes_valid]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [GSYM
           compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_center_boxes_encode,
         GSYM
           compute_boundedCase16594ObjectFirstPolyEnvironmentBridgeTheory.bounded_case16594_object_cell0_outer_boxes_encode,
         GSYM
           compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_case16594_object_cell0_runtime_radii_encode]
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_source5_dispatch_runtime_refines:
  bounded_object_q_taylor_stack_runtime_refines
      runtime_stack semantic_stack /\
  4110 < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv bounded_case16594_object_cell0_center_boxes_cv;
         from_cv bounded_case16594_object_cell0_outer_boxes_cv;
         from_cv bounded_case16594_object_cell0_radii_cv;
         from_cv (Num 0);
         from_cv bounded_case16594_object_cell0_source5_cv;
         from_cv certificates;
         from_cv (bounded_object_q_cv_list runtime_stack)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_object_q_cv_list (runtime_result::runtime_stack))
            certificates))),refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack)
      (bounded_case16594_object_source5_result::semantic_stack)
Proof
  strip_tac
  >> irule bounded_case16594_object_cell0_dispatch_poly_eval_runtime_refines
  >> conj_tac
  >- (qexists_tac `bounded_case16594_object_source5_poly_program`
      >> simp
           [compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_source5_decodes,
            bounded_case16594_object_source5_semantic_trace,
            compute_boundedCase16594ObjectPrefix8IdentityTheory.bounded_case16594_object_source5_poly_program_def]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
