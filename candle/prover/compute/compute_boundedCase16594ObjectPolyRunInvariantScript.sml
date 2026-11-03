(*****************************************************************************
 * Whole-program runtime/semantic invariant for object-q polynomial blocks.
 *
 * The production runner evaluates a canonical cv instruction list and
 * threads a tagged runtime stack.  This theory lifts the one-instruction
 * bridge through that actual recursive evaluator, choosing each next runtime
 * stack at the clock at which the step is executed.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyRunInvariant
Ancestors
  compute_boundedCase16594ObjectPolyStepInvariant
  compute_boundedCase16594ObjectPolyTraceEval
  compute_boundedAnalyticObjectPolyRunRefinement
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_poly_run_eval_runtime_refines:
  !semantic_program semantic_stack semantic_result_stack runtime_stack
      clock refs.
    EVERY bounded_object_q_encoded runtime_radii /\
    LENGTH runtime_radii = 6 /\
    bounded_taylor_radius_pairs semantic_radii = SOME weights /\
    LIST_REL bounded_case10173_q_cv_equiv runtime_radii
      (MAP bounded_word64_object_q_cv semantic_radii) /\
    LENGTH runtime_center_boxes = 6 /\
    LENGTH runtime_outer_boxes = 6 /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_center_boxes semantic_center_boxes /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_outer_boxes semantic_outer_boxes /\
    EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
    EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
    bounded_object_q_taylor_stack_runtime_refines
      runtime_stack semantic_stack /\
    bounded_object_q_poly_run semantic_radii weights
      semantic_center_boxes semantic_outer_boxes semantic_program
      semantic_stack = SOME semantic_result_stack /\
    4102 + LENGTH semantic_program + 1 < clock ==>
    ?runtime_result_stack.
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_poly_run»
          [from_cv (bounded_object_q_cv_list runtime_center_boxes);
           from_cv (bounded_object_q_cv_list runtime_outer_boxes);
           from_cv (bounded_object_q_cv_list runtime_radii);
           from_cv
             (bounded_object_q_cv_list
               (MAP bounded_object_q_poly_instruction_cv
                 semantic_program));
           from_cv
             (Pair (compute_exec$Num 1)
               (bounded_object_q_cv_list runtime_stack))])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1)
            (bounded_object_q_cv_list runtime_result_stack))),refs) /\
      bounded_object_q_taylor_stack_runtime_refines
        runtime_result_stack semantic_result_stack
Proof
  Induct_on `semantic_program`
  >- (rpt gen_tac
      >> simp
           [compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> strip_tac
      >> gvs []
      >> qexists_tac `runtime_stack`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST
                [`center_boxes` |->
                   `bounded_object_q_cv_list runtime_center_boxes`,
                 `outer_boxes` |->
                   `bounded_object_q_cv_list runtime_outer_boxes`,
                 `radii` |-> `bounded_object_q_cv_list runtime_radii`,
                 `nil` |-> `0`,
                 `execution` |->
                   `Pair (compute_exec$Num 1)
                      (bounded_object_q_cv_list runtime_stack)`]
                compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_poly_run_nil_eval))
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> rpt gen_tac
  >> Cases_on
       `bounded_object_q_poly_step semantic_radii weights
          semantic_center_boxes semantic_outer_boxes h semantic_stack`
  >> gvs
       [compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_object_q_poly_run_def]
  >> strip_tac
  >> rename1
       `bounded_object_q_poly_step semantic_radii weights
          semantic_center_boxes semantic_outer_boxes h semantic_stack =
        SOME semantic_next_stack`
  >> mp_tac
       (Q.INST
         [`semantic_instruction` |-> `h`,
          `semantic_stack` |-> `semantic_stack`,
          `semantic_result_stack` |-> `semantic_next_stack`,
          `runtime_stack` |-> `runtime_stack`,
          `clock` |-> `clock - 1`,
          `refs` |-> `refs`]
         compute_boundedCase16594ObjectPolyStepInvariantTheory.bounded_case16594_object_poly_instruction_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then
       (qx_choose_then `runtime_next_stack` strip_assume_tac)
  >> first_x_assum
       (qspecl_then
         [`semantic_next_stack`,`semantic_result_stack`,
          `runtime_next_stack`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then
       (qx_choose_then `runtime_result_stack` strip_assume_tac)
  >> qexists_tac `runtime_result_stack`
  >> conj_tac
  >- (sg `0 < clock` >- intLib.ARITH_TAC
      >> PURE_REWRITE_TAC
           [compute_execTheory.from_cv_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
      >> PURE_ONCE_REWRITE_TAC
           [MATCH_MP
             (SIMP_RULE std_ss
                [compute_execTheory.from_cv_def,
                 compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
               (Q.INST
                 [`center_boxes` |->
                    `bounded_object_q_cv_list runtime_center_boxes`,
                  `outer_boxes` |->
                    `bounded_object_q_cv_list runtime_outer_boxes`,
                  `radii` |-> `bounded_object_q_cv_list runtime_radii`,
                  `instructions` |->
                    `bounded_object_q_cv_list
                      (bounded_object_q_poly_instruction_cv h ::
                       MAP bounded_object_q_poly_instruction_cv
                         semantic_program)`,
                  `execution` |->
                    `Pair (compute_exec$Num 1)
                      (bounded_object_q_cv_list runtime_stack)`,
                  `refs` |-> `refs`,
                  `clock` |-> `clock`]
                 compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_poly_run_unfold))
             (ASSUME ``0:num < clock``)]
      >> PURE_ONCE_REWRITE_TAC
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`center_boxes` |->
                  `bounded_object_q_cv_list runtime_center_boxes`,
                `outer_boxes` |->
                  `bounded_object_q_cv_list runtime_outer_boxes`,
                `radii` |-> `bounded_object_q_cv_list runtime_radii`,
                `instruction` |->
                  `bounded_object_q_poly_instruction_cv h`,
                `rest` |->
                  `bounded_object_q_cv_list
                    (MAP bounded_object_q_poly_instruction_cv
                      semantic_program)`,
                `stack` |-> `bounded_object_q_cv_list runtime_stack`,
                `refs` |-> `refs`,
                `clock` |-> `clock - 1`]
               compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_poly_run_cons_success_control_eval)]
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_object_poly_run»
                [from_cv (bounded_object_q_cv_list runtime_center_boxes);
                 from_cv (bounded_object_q_cv_list runtime_outer_boxes);
                 from_cv (bounded_object_q_cv_list runtime_radii);
                 from_cv
                   (bounded_object_q_cv_list
                     (MAP bounded_object_q_poly_instruction_cv
                       semantic_program));
                 from_cv
                   (Pair (compute_exec$Num 1)
                     (bounded_object_q_cv_list runtime_next_stack))]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectPolyTraceEvalTheory.bounded_case16594_object_compute_eval_app5_argument_results
          >> simp [compute_execProofTheory.compute_eval_from_cv]
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [compute_execTheory.from_cv_def])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
