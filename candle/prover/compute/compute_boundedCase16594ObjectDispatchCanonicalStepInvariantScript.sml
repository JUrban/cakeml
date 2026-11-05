(*****************************************************************************
 * Canonical-source adapters from object semantic steps to the uniform
 * production dispatcher trace interface.
 *
 * These lemmas eliminate representation bookkeeping from the eventual list
 * induction.  The first packet covers the certificate-free negation family;
 * the remaining ordinary and specialized families use the same interface.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCanonicalStepInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchCanonicalSourceIdentity
  compute_boundedCase16594ObjectDispatchCell0TraceContract
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_canonical_neg_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Neg /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Neg
    (semantic_stack,semantic_certificates) semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack) runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> Cases_on `semantic_stack`
  >- gvs
      [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
       compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> Cases_on `runtime_stack`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1
       `bounded_object_q_taylor_stack_runtime_refines
          (runtime_head::runtime_tail) (semantic_head::semantic_tail)`
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     bounded_case16594_analytic_instruction_cv_def]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_state` |-> `runtime_head`,
          `semantic_state` |-> `semantic_head`,
          `runtime_rest` |-> `runtime_tail`,
          `semantic_rest` |-> `semantic_tail`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `runtime_certificates`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `semantic_certificates` |-> `semantic_certificates`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_neg_dispatch_stack_eval_above)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result::runtime_tail`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `4106`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_canonical_add_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Add /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Add
    (semantic_stack,semantic_certificates) semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack) runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> Cases_on `semantic_stack`
  >- gvs
      [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
       compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> rename1 `semantic_right::semantic_tail`
  >> Cases_on `semantic_tail`
  >- gvs
      [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
       compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> rename1 `semantic_right::semantic_left::semantic_rest`
  >> Cases_on `runtime_stack`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1 `runtime_right::runtime_tail`
  >> Cases_on `runtime_tail`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1 `runtime_right::runtime_left::runtime_rest`
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     bounded_case16594_analytic_instruction_cv_def,
     compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
     LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`runtime_right` |-> `runtime_right`,
          `semantic_right` |-> `semantic_right`,
          `runtime_left` |-> `runtime_left`,
          `semantic_left` |-> `semantic_left`,
          `runtime_rest` |-> `runtime_rest`,
          `semantic_rest` |-> `semantic_rest`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `runtime_certificates`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `semantic_certificates` |-> `semantic_certificates`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_add_dispatch_stack_eval_above)
  >> impl_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result::runtime_rest`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `4106`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_canonical_mul_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Mul /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Mul
    (semantic_stack,semantic_certificates) semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack) runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> Cases_on `semantic_stack`
  >- gvs
      [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
       compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> rename1 `semantic_right::semantic_tail`
  >> Cases_on `semantic_tail`
  >- gvs
      [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
       compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> rename1 `semantic_right::semantic_left::semantic_rest`
  >> Cases_on `runtime_stack`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1 `runtime_right::runtime_tail`
  >> Cases_on `runtime_tail`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1 `runtime_right::runtime_left::runtime_rest`
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     bounded_case16594_analytic_instruction_cv_def,
     compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
     LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`runtime_right` |-> `runtime_right`,
          `semantic_right` |-> `semantic_right`,
          `runtime_left` |-> `runtime_left`,
          `semantic_left` |-> `semantic_left`,
          `runtime_rest` |-> `runtime_rest`,
          `semantic_rest` |-> `semantic_rest`,
          `runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `certificates` |-> `runtime_certificates`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `semantic_certificates` |-> `semantic_certificates`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_mul_dispatch_stack_eval_above)
  >> impl_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result::runtime_rest`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `4106`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
        LIST_REL_def]
QED

Theorem bounded_case16594_object_canonical_square_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Square /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Square
    (semantic_stack,semantic_certificates) semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack) runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> Cases_on `semantic_stack`
  >- gvs
      [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
       compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
       compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> Cases_on `runtime_stack`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     bounded_case16594_analytic_instruction_cv_def]
  >> metis_tac
    [compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_square_dispatch_stack_eval_above,
     compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken,
     compute_boundedCase16594ObjectDispatchCell0TraceContractTheory.bounded_case16594_object_dispatch_common_floor_dominates_fixed]
QED

Theorem bounded_case16594_object_canonical_pi_half_step_eval_above:
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64PiHalf /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64PiHalf
    (semantic_stack,semantic_certificates) semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes radii (Num 0)
      (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack) runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> gvs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def,
     compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     bounded_case16594_analytic_instruction_cv_def]
  >> mp_tac
       (Q.INST
         [`runtime_stack` |-> `runtime_stack`,
          `semantic_stack` |-> `semantic_stack`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`, `radii` |-> `radii`,
          `certificates` |-> `runtime_certificates`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `semantic_certificates` |-> `semantic_certificates`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_pi_half_dispatch_stack_eval_above)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexists_tac
       `bounded_case16594_object_pi_half_runtime_cv::runtime_stack`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `4106`
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> fs
       [compute_boundedCase16594ObjectPiHalfInvariantTheory.bounded_case16594_object_pi_half_semantic_def]
QED

Theorem bounded_case16594_object_canonical_poly_step_eval_above:
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
  bounded_analytic_instruction_refines 6 source
    (BoundedAnalytic64Polynomial prepared_program) /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source
    (BoundedAnalytic64Polynomial prepared_program)
    (semantic_stack,semantic_certificates) semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack /\
  (case source of
   | BoundedAnalyticPolynomial source_program =>
       4105 + LENGTH source_program <= 524405
   | _ => F)
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      (bounded_object_q_cv_list runtime_center_boxes)
      (bounded_object_q_cv_list runtime_outer_boxes)
      (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      runtime_certificates (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack) runtime_certificates /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificates
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def]
  >> rename1
       `bounded_object_q_poly_run semantic_radii weights semantic_center_boxes
          semantic_outer_boxes source_program [] = SOME [semantic_result]`
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
          `runtime_source` |->
            `bounded_case16594_analytic_instruction_cv
              (BoundedAnalyticPolynomial source_program)`,
          `semantic_program` |-> `source_program`,
          `semantic_result` |-> `semantic_result`,
          `certificates` |-> `runtime_certificates`,
          `semantic_certificates` |-> `semantic_certificates`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_poly_dispatch_stack_eval_above)
  >> impl_tac
  >- asm_simp_tac std_ss
       [bounded_case16594_analytic_instruction_cv_round_trip]
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> `4105 + LENGTH source_program <= 524405` by intLib.ARITH_TAC
  >> metis_tac
       [compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken]
QED

val _ = export_theory ();
