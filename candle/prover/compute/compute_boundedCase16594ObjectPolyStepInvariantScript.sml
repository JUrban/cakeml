(*****************************************************************************
 * One-instruction runtime/semantic invariant for object-q polynomial blocks.
 *
 * The production evaluator consumes the authenticated cv encoding while the
 * reusable semantics consumes bounded_poly_instruction.  This theory first
 * proves that successful source decoding fixes the exact production encoding,
 * then composes the per-opcode evaluator bridges under one stack invariant.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyStepInvariant
Ancestors
  compute_boundedCase16594ObjectPolyStackInvariant
  compute_boundedAnalyticProgramCV
Libs
  bossLib preamble intLib

Definition bounded_object_q_poly_instruction_cv_def:
  bounded_object_q_poly_instruction_cv
      (BoundedPolyConstant positive negative denominator_predecessor) =
    Pair (Num 0)
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor) /\
  bounded_object_q_poly_instruction_cv (BoundedPolyVariable index) =
    Pair (Num 1) (Num index) /\
  bounded_object_q_poly_instruction_cv BoundedPolyNeg = Num 2 /\
  bounded_object_q_poly_instruction_cv BoundedPolyAdd = Num 3 /\
  bounded_object_q_poly_instruction_cv BoundedPolyMul = Num 4 /\
  bounded_object_q_poly_instruction_cv BoundedPolySquare = Num 5
End

Theorem bounded_poly_instruction_of_cv_canonical:
  bounded_poly_instruction_of_cv runtime_instruction =
      SOME semantic_instruction ==>
  runtime_instruction =
    bounded_object_q_poly_instruction_cv semantic_instruction
Proof
  Cases_on `semantic_instruction`
  >> Cases_on `runtime_instruction`
  >> simp
       [compute_boundedAnalyticProgramCVTheory.bounded_poly_instruction_of_cv_def,
        compute_boundedAnalyticProgramCVTheory.bounded_rational_of_cv_def,
        bounded_object_q_poly_instruction_cv_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_analytic_source_q_cv_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_q_nth_some_lt:
  !values index value.
    bounded_object_q_nth values index = SOME value ==>
    index < LENGTH values
Proof
  Induct
  >> Cases_on `index`
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_nth_def]
QED

Theorem bounded_object_q_taylor_variable_some_lt:
  bounded_object_q_taylor_variable center_environment box_environment index =
      SOME result ==>
  index < LENGTH center_environment /\
  index < LENGTH box_environment
Proof
  rw
    [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_variable_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_object_q_nth_some_lt]
QED

Theorem bounded_case16594_object_poly_step_constant_eval_runtime_refines:
  2 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_poly_step»
      [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
       from_cv
         (bounded_object_q_poly_instruction_cv
           (BoundedPolyConstant positive negative
             denominator_predecessor));
       from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (compute_exec$Num 1)
          (Pair
            (bounded_case16594_object_constant_state_cv
              (bounded_analytic_source_q_cv positive negative
                denominator_predecessor))
            stack))),refs) /\
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_constant_state_cv
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  strip_tac
  >> mp_tac
       compute_boundedCase16594ObjectPolyBaseStepSemanticEvalTheory.bounded_case16594_object_poly_step_constant_eval_semantic
  >> impl_tac >- simp []
  >> strip_tac
  >> conj_tac
  >- fs
       [bounded_object_q_poly_instruction_cv_def,
        compute_execTheory.from_cv_def]
  >> ACCEPT_TAC
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_constant_runtime_refines
QED

Theorem bounded_case16594_object_poly_step_variable_eval_runtime_refines:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  variable < 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  59 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv (bounded_object_q_cv_list runtime_center_boxes);
         from_cv (bounded_object_q_cv_list runtime_outer_boxes);
         from_cv radii;
         from_cv
           (bounded_object_q_poly_instruction_cv
             (BoundedPolyVariable variable));
         from_cv stack]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (compute_exec$Num 1)
          (Pair
            (bounded_case16594_object_variable_state_cv
              runtime_center_boxes runtime_outer_boxes variable)
            stack))),refs) /\
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_variable_state_cv
      runtime_center_boxes runtime_outer_boxes variable)
    (THE
      (bounded_object_q_taylor_variable
        semantic_center_boxes semantic_outer_boxes variable))
Proof
  strip_tac
  >> conj_tac
  >- (mp_tac
        (Q.INST
          [`semantic_center_boxes` |-> `semantic_center_boxes`,
           `semantic_outer_boxes` |-> `semantic_outer_boxes`]
          compute_boundedCase16594ObjectPolyVariableStepSemanticEvalTheory.bounded_case16594_object_poly_step_variable_eval_semantic)
      >> impl_tac >- simp []
      >> simp
           [bounded_object_q_poly_instruction_cv_def,
            compute_execTheory.from_cv_def])
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_variable_runtime_refines
  >> simp []
QED

Theorem bounded_object_q_taylor_variable_runtime_refines_some:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  variable < 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes /\
  bounded_object_q_taylor_variable
    semantic_center_boxes semantic_outer_boxes variable = SOME result ==>
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_variable_state_cv
      runtime_center_boxes runtime_outer_boxes variable)
    result
Proof
  strip_tac
  >> mp_tac
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_variable_runtime_refines
  >> impl_tac >- simp []
  >> simp []
QED

Theorem bounded_case16594_object_poly_instruction_eval_runtime_refines:
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
  bounded_object_q_poly_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes semantic_instruction
    semantic_stack = SOME semantic_result_stack /\
  4102 < clock ==>
  ?runtime_result_stack.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv (bounded_object_q_cv_list runtime_center_boxes);
         from_cv (bounded_object_q_cv_list runtime_outer_boxes);
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv
           (bounded_object_q_poly_instruction_cv semantic_instruction);
         from_cv (bounded_object_q_cv_list runtime_stack)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (compute_exec$Num 1)
          (bounded_object_q_cv_list runtime_result_stack))),refs) /\
    bounded_object_q_taylor_stack_runtime_refines
      runtime_result_stack semantic_result_stack
Proof
  Cases_on `semantic_instruction`
  >> strip_tac
  >- (fs
        [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> qexists_tac
           `bounded_case16594_object_constant_state_cv
              (bounded_analytic_source_q_cv n n0 n1)::runtime_stack`
      >> conj_tac
      >- (mp_tac
            (Q.INST
              [`positive` |-> `n`,
               `negative` |-> `n0`,
               `denominator_predecessor` |-> `n1`,
               `center_boxes` |->
                 `bounded_object_q_cv_list runtime_center_boxes`,
               `outer_boxes` |->
                 `bounded_object_q_cv_list runtime_outer_boxes`,
               `radii` |-> `bounded_object_q_cv_list runtime_radii`,
               `stack` |-> `bounded_object_q_cv_list runtime_stack`]
              bounded_case16594_object_poly_step_constant_eval_runtime_refines)
          >> impl_tac >- intLib.ARITH_TAC
          >> simp
               [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
                compute_execTheory.from_cv_def])
      >> gvs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_constant_runtime_refines])
  >- (Cases_on
        `bounded_object_q_taylor_variable
           semantic_center_boxes semantic_outer_boxes n`
      >> gvs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> `n < 6` by
           metis_tac
             [bounded_object_q_taylor_variable_some_lt,LIST_REL_LENGTH]
      >> qexists_tac
           `bounded_case16594_object_variable_state_cv
              runtime_center_boxes runtime_outer_boxes n::runtime_stack`
      >> conj_tac
      >- (mp_tac
            (Q.INST
              [`variable` |-> `n`,
               `radii` |-> `bounded_object_q_cv_list runtime_radii`,
               `stack` |-> `bounded_object_q_cv_list runtime_stack`]
              bounded_case16594_object_poly_step_variable_eval_runtime_refines)
          >> impl_tac >- (simp [] >> intLib.ARITH_TAC)
          >> simp
               [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
                compute_execTheory.from_cv_def])
      >> gvs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> simp
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> conj_tac
      >- (irule bounded_object_q_taylor_variable_runtime_refines_some
          >> simp []
          >> qexists_tac `semantic_center_boxes`
          >> qexists_tac `semantic_outer_boxes`
          >> simp [])
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def])
  >- (Cases_on `semantic_stack`
      >- fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              runtime_stack (semantic_state::semantic_rest)`
      >> Cases_on `runtime_stack`
      >- fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              (runtime_state::runtime_rest)
              (semantic_state::semantic_rest)`
      >> fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> mp_tac
           (Q.INST
             [`center_boxes` |->
                `bounded_object_q_cv_list runtime_center_boxes`,
              `outer_boxes` |->
                `bounded_object_q_cv_list runtime_outer_boxes`,
              `rest` |-> `bounded_object_q_cv_list runtime_rest`]
             compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_neg_eval_runtime_refines)
      >> impl_tac >- simp []
      >> disch_then (qx_choose_then `result_state` strip_assume_tac)
      >> qexists_tac `result_state::runtime_rest`
      >> gvs
           [bounded_object_q_poly_instruction_cv_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_execTheory.from_cv_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def])
  >- (Cases_on `semantic_stack`
      >- fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              runtime_stack (semantic_right::semantic_tail)`
      >> Cases_on `semantic_tail`
      >- fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              runtime_stack
              (semantic_right::semantic_left::semantic_rest)`
      >> Cases_on `runtime_stack`
      >- fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              (runtime_right::runtime_tail)
              (semantic_right::semantic_left::semantic_rest)`
      >> Cases_on `runtime_tail`
      >- fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              (runtime_right::runtime_left::runtime_rest)
              (semantic_right::semantic_left::semantic_rest)`
      >> fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> mp_tac
           (Q.INST
             [`center_boxes` |->
                `bounded_object_q_cv_list runtime_center_boxes`,
              `outer_boxes` |->
                `bounded_object_q_cv_list runtime_outer_boxes`,
              `runtime_left_state` |-> `runtime_left`,
              `runtime_right_state` |-> `runtime_right`,
              `semantic_left_state` |-> `semantic_left`,
              `semantic_right_state` |-> `semantic_right`,
              `rest` |-> `bounded_object_q_cv_list runtime_rest`]
             compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_add_eval_runtime_refines)
      >> impl_tac >- simp []
      >> disch_then (qx_choose_then `result_state` strip_assume_tac)
      >> qexists_tac `result_state::runtime_rest`
      >> gvs
           [bounded_object_q_poly_instruction_cv_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_execTheory.from_cv_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def])
  >- (Cases_on `semantic_stack`
      >- fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              runtime_stack (semantic_right::semantic_tail)`
      >> Cases_on `semantic_tail`
      >- fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              runtime_stack
              (semantic_right::semantic_left::semantic_rest)`
      >> Cases_on `runtime_stack`
      >- fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              (runtime_right::runtime_tail)
              (semantic_right::semantic_left::semantic_rest)`
      >> Cases_on `runtime_tail`
      >- fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> rename1
           `bounded_object_q_taylor_stack_runtime_refines
              (runtime_right::runtime_left::runtime_rest)
              (semantic_right::semantic_left::semantic_rest)`
      >> fs
           [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
      >> mp_tac
           (Q.INST
             [`center_boxes` |->
                `bounded_object_q_cv_list runtime_center_boxes`,
              `outer_boxes` |->
                `bounded_object_q_cv_list runtime_outer_boxes`,
              `runtime_left_state` |-> `runtime_left`,
              `runtime_right_state` |-> `runtime_right`,
              `semantic_left_state` |-> `semantic_left`,
              `semantic_right_state` |-> `semantic_right`,
              `rest` |-> `bounded_object_q_cv_list runtime_rest`]
             compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_mul_eval_runtime_refines)
      >> impl_tac >- simp []
      >> disch_then (qx_choose_then `result_state` strip_assume_tac)
      >> qexists_tac `result_state::runtime_rest`
      >> gvs
           [bounded_object_q_poly_instruction_cv_def,
            compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
            compute_execTheory.from_cv_def,
            compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def])
  >> Cases_on `semantic_stack`
  >- fs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def]
  >> rename1
       `bounded_object_q_taylor_stack_runtime_refines
          runtime_stack (semantic_state::semantic_rest)`
  >> Cases_on `runtime_stack`
  >- fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
  >> rename1
       `bounded_object_q_taylor_stack_runtime_refines
          (runtime_state::runtime_rest)
          (semantic_state::semantic_rest)`
  >> fs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_poly_step_def,
        compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
  >> mp_tac
       (Q.INST
         [`center_boxes` |->
            `bounded_object_q_cv_list runtime_center_boxes`,
          `outer_boxes` |->
            `bounded_object_q_cv_list runtime_outer_boxes`,
          `rest` |-> `bounded_object_q_cv_list runtime_rest`]
         compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_case16594_object_poly_step_square_eval_runtime_refines)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state::runtime_rest`
  >> gvs
       [bounded_object_q_poly_instruction_cv_def,
        compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def,
        compute_execTheory.from_cv_def,
        compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def]
QED

val _ = export_theory ();
