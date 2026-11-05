(*****************************************************************************
 * Canonical certified-step adapters for the exact object dispatcher.
 *
 * The fixed-word checker keeps nonlinear witnesses in typed certificates,
 * while the exact object dispatcher consumes the corresponding intervals as
 * one flat cv list.  These lemmas make that representation boundary explicit.
 * The first bounded packet covers sqrt, the first certified instruction in
 * genuine case 16594.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchCanonicalCertifiedStepInvariant
Ancestors
  compute_boundedCase16594ObjectDispatchCanonicalStepInvariant
Libs
  bossLib preamble intLib

Theorem bounded_object_q_sqrt_certificate_exact_output_valid:
  bounded_object_q_sqrt_certificate_exact input output ==>
  bounded_packed_q_interval_valid_cv output
Proof
  rw
    [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_object_q_sqrt_certificate_exact_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> every_case_tac
  >> gvs
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_object_q_positive_inv_certificate_exact_output_valid:
  bounded_object_q_positive_inv_certificate_exact input output ==>
  bounded_packed_q_interval_valid_cv output
Proof
  rw
    [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_object_q_positive_inv_certificate_exact_def,
     compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> every_case_tac
  >> gvs
    [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
     compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_case16594_object_canonical_sqrt_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Sqrt /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Sqrt
    (semantic_stack,
     BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
       center_derivative box_derivative box_second_reciprocal::
       semantic_certificate_rest)
    semantic_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        ([bounded_interval64_object_q_cv center_sqrt;
          bounded_interval64_object_q_cv box_sqrt;
          bounded_interval64_object_q_cv center_derivative;
          bounded_interval64_object_q_cv box_derivative;
          bounded_interval64_object_q_cv box_second_reciprocal] ++
         runtime_certificate_rest))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificate_rest
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
  >> Cases_on `h`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_value object_gradient_bounds object_hessian`
  >> Cases_on `runtime_stack`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1
       `bounded_object_q_taylor_stack_runtime_refines
          (runtime_head::runtime_tail)
          (BoundedObjectQTaylor object_domain object_center
             object_center_gradient object_value object_gradient_bounds
             object_hessian::semantic_tail)`
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_instruction_cv_def]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_center_root` |->
            `bounded_interval64_object_q_cv center_sqrt`,
          `runtime_box_root` |->
            `bounded_interval64_object_q_cv box_sqrt`,
          `runtime_center_derivative` |->
            `bounded_interval64_object_q_cv center_derivative`,
          `runtime_box_derivative` |->
            `bounded_interval64_object_q_cv box_derivative`,
          `runtime_box_second_reciprocal` |->
            `bounded_interval64_object_q_cv box_second_reciprocal`,
          `word_center_root` |-> `center_sqrt`,
          `word_box_root` |-> `box_sqrt`,
          `word_center_derivative` |-> `center_derivative`,
          `word_box_derivative` |-> `box_derivative`,
          `word_box_second_reciprocal` |-> `box_second_reciprocal`,
          `runtime_certificate_rest` |-> `runtime_certificate_rest`,
          `runtime_state` |-> `runtime_head`,
          `runtime_rest` |-> `runtime_tail`,
          `semantic_state` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_value object_gradient_bounds
               object_hessian`,
          `semantic_rest` |-> `semantic_tail`,
          `semantic_certificate_rest` |-> `semantic_certificate_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`,
          `source_payload` |-> `bounded_sqrt_placeholder_cv`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_sqrt_dispatch_stack_eval_above)
  >> impl_tac
  >- (asm_simp_tac (srw_ss())
        [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
         compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def]
      >> metis_tac
           [bounded_object_q_sqrt_certificate_exact_output_valid,
            bounded_object_q_positive_inv_certificate_exact_output_valid])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result::runtime_tail`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `8213`
      >> conj_tac
      >- simp []
      >> fs [])
  >> first_assum ACCEPT_TAC
QED

Theorem bounded_case16594_object_canonical_inverse_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Inverse /\
  bounded_object_q_analytic_step semantic_radii weights
    semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Inverse
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_value object_gradient_bounds object_hessian::semantic_tail,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       semantic_certificate_rest)
    semantic_next /\
  bounded_object_q_positive_inv_certificate_exact object_center
    (bounded_interval64_object_q_cv center_reciprocal) /\
  bounded_object_q_positive_inv_certificate_exact object_value
    (bounded_interval64_object_q_cv box_reciprocal) /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_value object_gradient_bounds object_hessian::semantic_tail)
  ==>
  ?next_runtime_stack.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        ([bounded_interval64_object_q_cv center_reciprocal;
          bounded_interval64_object_q_cv box_reciprocal] ++
         runtime_certificate_rest))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificate_rest
Proof
  PairCases_on `semantic_next`
  >> strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> Cases_on `runtime_stack`
  >- fs
      [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_stack_runtime_refines_def,
       LIST_REL_def]
  >> rename1
       `bounded_object_q_taylor_stack_runtime_refines
          (runtime_head::runtime_tail)
          (BoundedObjectQTaylor object_domain object_center
             object_center_gradient object_value object_gradient_bounds
             object_hessian::semantic_tail)`
  >> gvs
    [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
     compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def,
     compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_object_q_analytic_ordinary_step_def,
     compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_instruction_cv_def]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_center_reciprocal` |->
            `bounded_interval64_object_q_cv center_reciprocal`,
          `runtime_box_reciprocal` |->
            `bounded_interval64_object_q_cv box_reciprocal`,
          `word_center_reciprocal` |-> `center_reciprocal`,
          `word_box_reciprocal` |-> `box_reciprocal`,
          `runtime_certificate_rest` |-> `runtime_certificate_rest`,
          `runtime_state` |-> `runtime_head`,
          `runtime_rest` |-> `runtime_tail`,
          `semantic_state` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_value object_gradient_bounds
               object_hessian`,
          `semantic_rest` |-> `semantic_tail`,
          `semantic_certificate_rest` |-> `semantic_certificate_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_inverse_dispatch_stack_eval_above)
  >> impl_tac
  >- (asm_simp_tac (srw_ss())
        [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
         compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def]
      >> metis_tac
           [bounded_object_q_positive_inv_certificate_exact_output_valid])
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result::runtime_tail`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `8213`
      >> conj_tac
      >- simp []
      >> fs [])
  >> first_assum ACCEPT_TAC
QED

Theorem bounded_case16594_object_canonical_atan_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Atan /\
  bounded_packed_q_interval_valid_cv
    (bounded_interval64_object_q_cv center_result) /\
  bounded_packed_q_interval_valid_cv
    (bounded_interval64_object_q_cv center_derivative) /\
  bounded_packed_q_interval_valid_cv
    (bounded_interval64_object_q_cv box_derivative) /\
  bounded_packed_q_interval_valid_cv
    (bounded_interval64_object_q_cv box_derivative_square) /\
  bounded_object_q_interval_encoded
    (bounded_interval64_object_q_cv center_input) /\
  bounded_object_q_interval_encoded
    (bounded_interval64_object_q_cv box_input) /\
  bounded_interval64_atan_range center_input lower_reciprocal
    upper_reciprocal = SOME center_result /\
  bounded_object_q_interval_encloses
    (bounded_interval64_object_q_cv center_input)
    (bounded_object_q_taylor_center semantic_state) /\
  bounded_object_q_interval_encloses
    (bounded_interval64_object_q_cv box_input)
    (bounded_object_q_taylor_value_bound semantic_state) /\
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_center semantic_state)
    (bounded_interval64_object_q_cv center_input)
    (bounded_interval64_object_q_cv center_square) /\
  bounded_object_q_square_certificate_exact
    (bounded_object_q_taylor_value_bound semantic_state)
    (bounded_interval64_object_q_cv box_input)
    (bounded_interval64_object_q_cv box_square) /\
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv
      (bounded_interval64_object_q_cv center_square))
    (bounded_interval64_object_q_cv center_derivative) /\
  bounded_object_q_inv_certificate_exact
    (bounded_object_q_atan_denominator_cv
      (bounded_interval64_object_q_cv box_square))
    (bounded_interval64_object_q_cv box_derivative) /\
  bounded_object_q_square_certificate_exact
    (bounded_interval64_object_q_cv box_derivative)
    (bounded_interval64_object_q_cv box_derivative)
    (bounded_interval64_object_q_cv box_derivative_square) /\
  bounded_case16594_object_atan_fixed_pure_contract
    (bounded_interval64_object_q_cv center_input)
    (bounded_interval64_object_q_cv box_input)
    (bounded_interval64_object_q_cv center_result)
    (bounded_interval64_object_q_cv center_square)
    (bounded_interval64_object_q_cv center_derivative)
    (bounded_interval64_object_q_cv box_square)
    (bounded_interval64_object_q_cv box_derivative)
    (bounded_interval64_object_q_cv box_derivative_square) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_head::runtime_tail) (semantic_state::semantic_tail)
  ==>
  ?runtime_result.
    bounded_case16594_object_dispatch_step_eval_above 524405
      center_boxes outer_boxes (bounded_object_q_cv_list runtime_radii)
      (Num 0) (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        ([bounded_interval64_object_q_cv center_input;
          bounded_interval64_object_q_cv box_input;
          bounded_interval64_object_q_cv center_result;
          bounded_interval64_object_q_cv center_square;
          bounded_interval64_object_q_cv center_derivative;
          bounded_interval64_object_q_cv box_square;
          bounded_interval64_object_q_cv box_derivative;
          bounded_interval64_object_q_cv box_derivative_square] ++
         runtime_certificate_rest))
      (bounded_object_q_cv_list (runtime_head::runtime_tail))
      (bounded_object_q_cv_list (runtime_result::runtime_tail))
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Atan
      (semantic_state::semantic_tail,
       BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
         center_derivative box_derivative::semantic_certificate_rest)
      (bounded_object_q_taylor_atan semantic_radii weights
         (bounded_interval64_object_q_cv center_result)
         (bounded_interval64_object_q_cv center_derivative)
         (bounded_interval64_object_q_cv box_derivative)
         (bounded_interval64_object_q_cv box_derivative_square)
         semantic_state::semantic_tail,
       semantic_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_tail)
      (bounded_object_q_taylor_atan semantic_radii weights
         (bounded_interval64_object_q_cv center_result)
         (bounded_interval64_object_q_cv center_derivative)
         (bounded_interval64_object_q_cv box_derivative)
         (bounded_interval64_object_q_cv box_derivative_square)
         semantic_state::semantic_tail)
Proof
  strip_tac
  >> fs
    [compute_boundedAnalyticPreparedPlanRefinementTheory.bounded_analytic_instruction_refines_def]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `runtime_center_input` |->
            `bounded_interval64_object_q_cv center_input`,
          `runtime_box_input` |->
            `bounded_interval64_object_q_cv box_input`,
          `runtime_center_result` |->
            `bounded_interval64_object_q_cv center_result`,
          `runtime_center_square` |->
            `bounded_interval64_object_q_cv center_square`,
          `runtime_center_derivative` |->
            `bounded_interval64_object_q_cv center_derivative`,
          `runtime_box_square` |->
            `bounded_interval64_object_q_cv box_square`,
          `runtime_box_derivative` |->
            `bounded_interval64_object_q_cv box_derivative`,
          `runtime_box_derivative_square` |->
            `bounded_interval64_object_q_cv box_derivative_square`,
          `word_center_input` |-> `center_input`,
          `word_box_input` |-> `box_input`,
          `word_center_result` |-> `center_result`,
          `word_center_square` |-> `center_square`,
          `word_center_derivative` |-> `center_derivative`,
          `word_box_square` |-> `box_square`,
          `word_box_derivative` |-> `box_derivative`,
          `word_box_derivative_square` |-> `box_derivative_square`,
          `word_lower_reciprocal` |-> `lower_reciprocal`,
          `word_upper_reciprocal` |-> `upper_reciprocal`,
          `runtime_certificate_rest` |-> `runtime_certificate_rest`,
          `runtime_state` |-> `runtime_head`,
          `runtime_rest` |-> `runtime_tail`,
          `semantic_state` |-> `semantic_state`,
          `semantic_rest` |-> `semantic_tail`,
          `semantic_certificate_rest` |-> `semantic_certificate_rest`,
          `center_boxes` |-> `center_boxes`,
          `outer_boxes` |-> `outer_boxes`]
         compute_boundedCase16594ObjectOrdinaryDispatchStepAboveInvariantTheory.bounded_case16594_object_atan_dispatch_stack_eval_above)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDispatchSemanticTraceTheory.bounded_case16594_object_dispatch_step_eval_above_weaken
      >> qexists_tac `16387`
      >> conj_tac
      >- simp []
      >> fs
        [compute_boundedCase16594ObjectDispatchCanonicalSourceIdentityTheory.bounded_case16594_analytic_instruction_cv_def])
  >> conj_tac
  >- (simp
       [compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_object_q_analytic_step_def,
        compute_boundedAnalyticObjectOrdinaryDispatcherRefinementTheory.bounded_analytic64_ordinary_instruction_def]
      >> first_assum ACCEPT_TAC)
  >> first_assum ACCEPT_TAC
QED

val _ = export_theory ();
