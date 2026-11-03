(*****************************************************************************
 * Reusable production ordinary-step invariant for polynomial instructions.
 *
 * A successful shared source decode fixes the exact canonical CV program.
 * The whole polynomial runner then supplies one related runtime result, and
 * the authenticated ordinary-step control flow prepends it to the existing
 * related outer stack.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectOrdinaryPolyInvariant
Ancestors
  compute_boundedCase16594ObjectPrefix8Identity
  compute_boundedCase16594ObjectPolyRunInvariant
Libs
  bossLib preamble intLib

Theorem bounded_poly_program_of_cv_canonical:
  !runtime_program semantic_program.
    bounded_poly_program_of_cv runtime_program = SOME semantic_program ==>
    runtime_program =
      bounded_object_q_cv_list
        (MAP bounded_object_q_poly_instruction_cv semantic_program)
Proof
  Induct_on `semantic_program`
  >> Cases_on `runtime_program`
  >> simp
       [compute_boundedAnalyticProgramCVTheory.bounded_poly_program_of_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> TRY
       (Cases_on `n`
        >> simp
             [compute_boundedAnalyticProgramCVTheory.bounded_poly_program_of_cv_def])
  >> TRY
       (strip_tac
        >> imp_res_tac
             compute_boundedCase16594ObjectPolyStepInvariantTheory.bounded_poly_instruction_of_cv_canonical)
QED

Theorem bounded_analytic_polynomial_source_canonical:
  bounded_analytic_instruction_of_cv runtime_source =
      SOME (BoundedAnalyticPolynomial semantic_program) ==>
  runtime_source =
    Pair (Num 0)
      (bounded_object_q_cv_list
        (MAP bounded_object_q_poly_instruction_cv semantic_program))
Proof
  Cases_on `runtime_source`
  >> simp
       [compute_boundedAnalyticProgramCVTheory.bounded_analytic_instruction_of_cv_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_poly_program_of_cv_canonical]
QED

Theorem bounded_case16594_object_ordinary_poly_eval_runtime_refines:
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
  bounded_analytic_instruction_of_cv runtime_source =
    SOME (BoundedAnalyticPolynomial semantic_program) /\
  bounded_object_q_poly_run semantic_radii weights
    semantic_center_boxes semantic_outer_boxes semantic_program [] =
      SOME [semantic_result] /\
  4104 + LENGTH semantic_program < clock ==>
  ?runtime_result.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv (bounded_object_q_cv_list runtime_center_boxes);
         from_cv (bounded_object_q_cv_list runtime_outer_boxes);
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv runtime_source;
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
      (runtime_result::runtime_stack) (semantic_result::semantic_stack)
Proof
  strip_tac
  >> drule bounded_analytic_polynomial_source_canonical
  >> strip_tac
  >> mp_tac
       (Q.SPECL
         [`semantic_program`, `[]`, `[semantic_result]`, `[]`,
          `clock - 1`, `refs`]
         (Q.INST
           [`runtime_radii` |-> `runtime_radii`,
            `semantic_radii` |-> `semantic_radii`,
            `weights` |-> `weights`,
            `runtime_center_boxes` |-> `runtime_center_boxes`,
            `runtime_outer_boxes` |-> `runtime_outer_boxes`,
            `semantic_center_boxes` |-> `semantic_center_boxes`,
            `semantic_outer_boxes` |-> `semantic_outer_boxes`]
           compute_boundedCase16594ObjectPolyRunInvariantTheory.bounded_case16594_object_poly_run_eval_runtime_refines))
  >> impl_tac
  >- (asm_rewrite_tac []
      >> simp
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> intLib.ARITH_TAC)
  >> disch_then
       (qx_choose_then `runtime_result_stack` strip_assume_tac)
  >> Cases_on `runtime_result_stack`
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def]
  >> qexists_tac `h`
  >> conj_tac
  >- (asm_rewrite_tac []
      >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_ordinary_poly_success_eval)
      >> conj_tac >- intLib.ARITH_TAC
      >> sg `0:num < clock - 1` >- intLib.ARITH_TAC
      >> PURE_ONCE_REWRITE_TAC
           [MATCH_MP
              (Q.INST
                [`clock` |-> `clock - 1`,
                 `center_boxes` |->
                   `bounded_object_q_cv_list runtime_center_boxes`,
                 `outer_boxes` |->
                   `bounded_object_q_cv_list runtime_outer_boxes`,
                 `radii` |-> `bounded_object_q_cv_list runtime_radii`,
                 `program` |->
                   `bounded_object_q_cv_list
                     (MAP bounded_object_q_poly_instruction_cv
                       semantic_program)`,
                 `refs` |-> `refs`]
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  compute_boundedCase16594ObjectFirstPolyDispatchBridgeTheory.bounded_case16594_object_poly_source_arguments_normalize))
              (ASSUME ``0:num < clock - 1``)]
      >> asm_rewrite_tac [])
  >> simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
