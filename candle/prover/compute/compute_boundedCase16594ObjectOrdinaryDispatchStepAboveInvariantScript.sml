(*****************************************************************************
 * Uniform clock-floor adapters for the ordinary case-16594 dispatcher.
 *
 * The operation-specific invariants already provide the exact runtime result,
 * analytic step, and stack refinement at any sufficiently large single
 * clock.  Successful compute evaluation is independent of the HOL reference
 * state and monotone in clock fuel, so one evaluation at the successor of the
 * operation floor supplies the uniform premise consumed by program traces.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariant
Ancestors
  compute_boundedCase16594ObjectAlgebraicDispatchInvariant
  compute_boundedCase16594ObjectOrdinaryPolyInvariant
  compute_boundedCase16594ObjectDispatchStepAboveEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_neg_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 2) certificates
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticNeg
      (semantic_state::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state::
         semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state::
         semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_neg_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_add_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 3) certificates
      (bounded_object_q_cv_list
        (runtime_right::runtime_left::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticAdd
      (semantic_right::semantic_left::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_add semantic_radii weights
         semantic_left semantic_right::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_add semantic_radii weights
         semantic_left semantic_right::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |-> `semantic_left`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |-> `semantic_right`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_add_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_mul_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_right::runtime_left::runtime_rest)
    (semantic_right::semantic_left::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 4) certificates
      (bounded_object_q_cv_list
        (runtime_right::runtime_left::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticMul
      (semantic_right::semantic_left::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_mul semantic_radii weights
         semantic_left semantic_right::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_mul semantic_radii weights
         semantic_left semantic_right::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_left_state` |-> `runtime_left`,
          `semantic_left_state` |-> `semantic_left`,
          `runtime_right_state` |-> `runtime_right`,
          `semantic_right_state` |-> `semantic_right`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_mul_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_square_dispatch_stack_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_state::runtime_rest) (semantic_state::semantic_rest) ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 4106
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (Num 5) certificates
      (bounded_object_q_cv_list (runtime_state::runtime_rest))
      (bounded_object_q_cv_list (runtime_result::runtime_rest)) certificates /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes BoundedAnalyticSquare
      (semantic_state::semantic_rest,semantic_certificates)
      (bounded_object_q_taylor_mul semantic_radii weights semantic_state
         semantic_state::semantic_rest,
       semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_rest)
      (bounded_object_q_taylor_mul semantic_radii weights semantic_state
         semantic_state::semantic_rest)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_state`,
          `semantic_state` |-> `semantic_state`,
          `stack_rest` |-> `bounded_object_q_cv_list runtime_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `certificates`,
          `clock` |-> `SUC 4106`, `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectAlgebraicDispatchInvariantTheory.bounded_case16594_object_square_dispatch_eval_runtime_refines)
  >> impl_tac
  >- (asm_rewrite_tac []
      >> fs
           [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
            LIST_REL_def])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> asm_rewrite_tac
           [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_cv_list_def])
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_poly_dispatch_stack_eval_above:
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
      SOME [semantic_result] ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above
      (4105 + LENGTH semantic_program)
      (bounded_object_q_cv_list runtime_center_boxes)
      (bounded_object_q_cv_list runtime_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 0) runtime_source certificates
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list (runtime_result::runtime_stack)) certificates /\
    bounded_object_q_analytic_ordinary_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes
      (BoundedAnalyticPolynomial semantic_program)
      (semantic_stack,semantic_certificates)
      (semantic_result::semantic_stack,semantic_certificates) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_stack) (semantic_result::semantic_stack)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_center_boxes` |-> `runtime_center_boxes`,
          `runtime_outer_boxes` |-> `runtime_outer_boxes`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_stack` |-> `runtime_stack`,
          `semantic_stack` |-> `semantic_stack`,
          `runtime_source` |-> `runtime_source`,
          `semantic_program` |-> `semantic_program`,
          `semantic_result` |-> `semantic_result`,
          `certificates` |-> `certificates`,
          `clock` |-> `SUC (4105 + LENGTH semantic_program) - 1`,
          `refs` |-> `(ARB:hol_refs)`]
         compute_boundedCase16594ObjectOrdinaryPolyInvariantTheory.bounded_case16594_object_ordinary_poly_eval_runtime_refines)
  >> impl_tac >- (asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchStepAboveEvalTheory.bounded_case16594_object_dispatch_step_eval_suc_to_above
      >> qexists_tac `ARB`
      >> irule
           compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_dispatch_ordinary_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- simp
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
