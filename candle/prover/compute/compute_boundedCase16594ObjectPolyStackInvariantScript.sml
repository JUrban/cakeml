(*****************************************************************************
 * Strong runtime/semantic invariant for production object-q polynomial
 * stacks.
 *
 * Numerical equivalence alone is not enough to invoke the production
 * operation bridges: subsequent steps also need the fixed six-/twenty-one-
 * field shape and packed-interval validity.  This theory records those facts
 * once and establishes the two stack-producing base cases.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyStackInvariant
Ancestors
  compute_boundedCase16594ObjectPolyBaseStepSemanticEval
  compute_boundedCase16594ObjectPolyVariableStepSemanticEval
  compute_boundedCase16594ObjectPolyAddStepSemanticEval
Libs
  bossLib preamble intLib

Definition bounded_object_q_taylor_semantic_valid_def:
  bounded_object_q_taylor_semantic_valid
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) <=>
    bounded_packed_q_interval_valid_cv center /\
    EVERY bounded_packed_q_interval_valid_cv center_gradient /\
    LENGTH center_gradient = 6 /\
    bounded_packed_q_interval_valid_cv value_bound /\
    EVERY bounded_packed_q_interval_valid_cv gradient_bounds /\
    LENGTH gradient_bounds = 6 /\
    EVERY bounded_packed_q_interval_valid_cv hessian /\
    LENGTH hessian = 21
End

Definition bounded_object_q_taylor_runtime_refines_def:
  bounded_object_q_taylor_runtime_refines runtime semantic <=>
    bounded_object_q_taylor_runtime_equiv runtime semantic /\
    bounded_object_q_taylor_semantic_valid semantic
End

Definition bounded_object_q_taylor_stack_runtime_refines_def:
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack <=>
    LIST_REL bounded_object_q_taylor_runtime_refines
      runtime_stack semantic_stack
End

Theorem bounded_object_q_interval_cv_equiv_left_encoded:
  bounded_object_q_interval_cv_equiv runtime semantic ==>
  bounded_object_q_interval_encoded runtime
Proof
  Cases_on `runtime`
  >> Cases_on `semantic`
  >> rw
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
        compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> fs
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_q_interval_list_rel_left_encoded:
  !runtime semantic.
    LIST_REL bounded_object_q_interval_cv_equiv runtime semantic ==>
    EVERY bounded_object_q_interval_encoded runtime
Proof
  Induct
  >> Cases_on `semantic`
  >> simp [LIST_REL_def]
  >> metis_tac [bounded_object_q_interval_cv_equiv_left_encoded]
QED

Theorem bounded_object_q_taylor_runtime_refines_shape:
  bounded_object_q_taylor_runtime_refines runtime
    (BoundedObjectQTaylor domain_flag center center_gradient value_bound
      gradient_bounds hessian) ==>
  ?runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime =
      bounded_case16594_object_state_cv
        (if domain_flag then Num 1 else Num 0)
        runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    bounded_object_q_interval_cv_equiv runtime_center center /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_center_gradient center_gradient /\
    bounded_object_q_interval_cv_equiv runtime_value_bound value_bound /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_gradient_bounds gradient_bounds /\
    LIST_REL bounded_object_q_interval_cv_equiv runtime_hessian hessian
Proof
  strip_tac
  >> fs
       [bounded_object_q_taylor_runtime_refines_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_encoded_cv_def]
  >> Cases_on `runtime`
  >- fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def]
  >> rename1 `Pair runtime_domain runtime_tail1`
  >> Cases_on `runtime_tail1`
  >- fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def]
  >> rename1 `Pair runtime_domain (Pair runtime_center runtime_tail2)`
  >> Cases_on `runtime_tail2`
  >- fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def]
  >> rename1
       `Pair runtime_domain
          (Pair runtime_center (Pair runtime_center_gradient_cv runtime_tail3))`
  >> Cases_on `runtime_tail3`
  >- fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def]
  >> rename1
       `Pair runtime_domain
          (Pair runtime_center
            (Pair runtime_center_gradient_cv
              (Pair runtime_value_bound runtime_tail4)))`
  >> Cases_on `runtime_tail4`
  >- fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def]
  >> rename1
       `Pair runtime_domain
          (Pair runtime_center
            (Pair runtime_center_gradient_cv
              (Pair runtime_value_bound
                (Pair runtime_gradient_bounds_cv runtime_hessian_cv))))`
  >> fs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_state_cv_equiv_def]
  >> imp_res_tac
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_cv_equiv_right_encoded
  >> metis_tac
       [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def]
QED

Theorem bounded_object_q_taylor_runtime_refines_contract:
  bounded_object_q_taylor_runtime_refines runtime
    (BoundedObjectQTaylor domain_flag center center_gradient value_bound
      gradient_bounds hessian) ==>
  ?runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime =
      bounded_case16594_object_state_cv
        (if domain_flag then Num 1 else Num 0)
        runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    bounded_object_q_interval_encoded runtime_center /\
    EVERY bounded_object_q_interval_encoded runtime_center_gradient /\
    LENGTH runtime_center_gradient = 6 /\
    bounded_object_q_interval_encoded runtime_value_bound /\
    EVERY bounded_object_q_interval_encoded runtime_gradient_bounds /\
    LENGTH runtime_gradient_bounds = 6 /\
    EVERY bounded_object_q_interval_encoded runtime_hessian /\
    LENGTH runtime_hessian = 21 /\
    bounded_object_q_interval_cv_equiv runtime_center center /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_center_gradient center_gradient /\
    bounded_object_q_interval_cv_equiv runtime_value_bound value_bound /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_gradient_bounds gradient_bounds /\
    LIST_REL bounded_object_q_interval_cv_equiv runtime_hessian hessian
Proof
  strip_tac
  >> drule bounded_object_q_taylor_runtime_refines_shape
  >> strip_tac
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> fs
       [bounded_object_q_taylor_runtime_refines_def,
        bounded_object_q_taylor_semantic_valid_def]
  >> metis_tac
       [bounded_object_q_interval_cv_equiv_left_encoded,
        bounded_object_q_interval_list_rel_left_encoded,
        LIST_REL_LENGTH]
QED

Theorem bounded_object_q_taylor_constant_semantic_valid:
  bounded_object_q_taylor_semantic_valid
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  simp
    [bounded_object_q_taylor_semantic_valid_def,
     compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_constant_def,
     compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_analytic_source_q_interval_valid,
     compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_zero]
QED

Theorem bounded_object_q_taylor_constant_runtime_refines:
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_constant_state_cv
      (bounded_analytic_source_q_cv positive negative
        denominator_predecessor))
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  simp
    [bounded_object_q_taylor_runtime_refines_def,
     bounded_object_q_taylor_constant_semantic_valid,
     compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_constant_runtime_semantic_equiv]
QED

Theorem bounded_object_q_unit_vector_semantic_valid:
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_unit_vector variable) /\
  LENGTH (bounded_object_q_unit_vector variable) = 6
Proof
  simp
    [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_unit_vector_def,
     EVERY_GENLIST]
  >> rpt COND_CASES_TAC
  >> simp
       [compute_boundedCase16594ObjectFirstNegSemanticEvalTheory.bounded_analytic_source_q_interval_valid]
QED

Theorem bounded_object_q_taylor_variable_semantic_valid:
  EVERY bounded_packed_q_interval_valid_cv center_environment /\
  LENGTH center_environment = 6 /\
  EVERY bounded_packed_q_interval_valid_cv box_environment /\
  LENGTH box_environment = 6 /\
  variable < 6 ==>
  bounded_object_q_taylor_semantic_valid
    (THE
      (bounded_object_q_taylor_variable
        center_environment box_environment variable))
Proof
  strip_tac
  >> `bounded_object_q_nth center_environment variable =
        SOME (EL variable center_environment)` by
       (irule
          compute_boundedCase16594ObjectVariableStateEvalTheory.bounded_case16594_object_nth_el
        >> intLib.ARITH_TAC)
  >> `bounded_object_q_nth box_environment variable =
        SOME (EL variable box_environment)` by
       (irule
          compute_boundedCase16594ObjectVariableStateEvalTheory.bounded_case16594_object_nth_el
        >> intLib.ARITH_TAC)
  >> `bounded_packed_q_interval_valid_cv
        (EL variable center_environment) /\
      bounded_packed_q_interval_valid_cv
        (EL variable box_environment)` by
       metis_tac [EVERY_EL]
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_variable_def,
        bounded_object_q_taylor_semantic_valid_def,
        bounded_object_q_unit_vector_semantic_valid,
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_zero]
QED

Theorem bounded_object_q_taylor_variable_runtime_refines:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  variable < 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_boxes /\
  EVERY bounded_packed_q_interval_valid_cv semantic_outer_boxes ==>
  bounded_object_q_taylor_runtime_refines
    (bounded_case16594_object_variable_state_cv
      runtime_center_boxes runtime_outer_boxes variable)
    (THE
      (bounded_object_q_taylor_variable
        semantic_center_boxes semantic_outer_boxes variable))
Proof
  strip_tac
  >> `LENGTH semantic_center_boxes = 6 /\
      LENGTH semantic_outer_boxes = 6` by
       metis_tac [LIST_REL_LENGTH]
  >> simp [bounded_object_q_taylor_runtime_refines_def]
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectVariableStateEvalTheory.bounded_case16594_object_variable_state_runtime_semantic_equiv
      >> simp [])
  >> irule bounded_object_q_taylor_variable_semantic_valid
  >> simp []
QED

Theorem bounded_object_q_dot_abs_upper_acc_cv_nonnegative_valid:
  !radii entries accumulator.
    LENGTH radii = LENGTH entries /\
    EVERY bounded_packed_q_interval_valid_cv entries /\
    bounded_object_q_nonnegative accumulator ==>
    bounded_object_q_nonnegative
      (bounded_object_q_dot_abs_upper_acc_cv radii entries accumulator)
Proof
  Induct
  >> Cases_on `entries`
  >> simp
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_dot_abs_upper_acc_cv_def]
  >> rpt strip_tac
  >> first_x_assum match_mp_tac
  >> simp []
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_add_cv_nonnegative
  >> simp []
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_mul_cv_nonnegative
  >> simp
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_nonnegative]
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_interval_abs_upper_cv_nonnegative
  >> fs
       [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> PairCases_on `decoded`
  >> simp []
QED

Theorem bounded_object_q_quadratic_contribution_cv_nonnegative_valid:
  bounded_packed_q_interval_valid_cv entry ==>
  bounded_object_q_nonnegative
    (bounded_object_q_quadratic_contribution_cv
      left_radius right_radius double entry)
Proof
  strip_tac
  >> `bounded_object_q_nonnegative
        (bounded_object_q_interval_abs_upper_cv entry)` by
       (irule
          compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_interval_abs_upper_cv_nonnegative
        >> fs
          [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
        >> PairCases_on `decoded`
        >> simp [])
  >> `bounded_object_q_nonnegative
        (bounded_object_q_mul_cv
          (bounded_word64_object_q_cv left_radius)
          (bounded_word64_object_q_cv right_radius))` by
       (irule
          compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_mul_cv_nonnegative
        >> simp
          [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_nonnegative])
  >> `bounded_object_q_nonnegative
        (bounded_object_q_mul_cv
          (bounded_object_q_mul_cv
            (bounded_word64_object_q_cv left_radius)
            (bounded_word64_object_q_cv right_radius))
          (bounded_object_q_interval_abs_upper_cv entry))` by
       (irule
          compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_mul_cv_nonnegative
        >> simp [])
  >> Cases_on `double`
  >> simp
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_contribution_cv_def,
        LET_THM]
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_add_cv_nonnegative
  >> simp []
QED

Theorem bounded_object_q_quadratic_abs_upper_acc_cv_nonnegative_valid:
  !weights entries accumulator.
    LENGTH weights = LENGTH entries /\
    EVERY bounded_packed_q_interval_valid_cv entries /\
    bounded_object_q_nonnegative accumulator ==>
    bounded_object_q_nonnegative
      (bounded_object_q_quadratic_abs_upper_acc_cv
        weights entries accumulator)
Proof
  Induct
  >- (Cases_on `entries`
      >> simp
        [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def])
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_quadratic_abs_upper_acc_cv_def]
  >> rpt strip_tac
  >> first_x_assum match_mp_tac
  >> simp []
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_add_cv_nonnegative
  >> simp [bounded_object_q_quadratic_contribution_cv_nonnegative_valid]
QED

Theorem bounded_object_q_taylor_error_cv_nonnegative_valid:
  LENGTH radii = LENGTH center_gradient /\
  LENGTH weights = LENGTH hessian /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv hessian ==>
  bounded_object_q_nonnegative
    (bounded_object_q_taylor_error_cv
      radii center_gradient weights hessian)
Proof
  strip_tac
  >> simp
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_error_cv_def,
        LET_THM]
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_add_cv_nonnegative
  >> conj_tac
  >- (irule
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_add_cv_nonnegative
      >> metis_tac
        [bounded_object_q_dot_abs_upper_acc_cv_nonnegative_valid,
         compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_nonnegative])
  >> metis_tac
       [bounded_object_q_quadratic_abs_upper_acc_cv_nonnegative_valid,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_nonnegative]
QED

Theorem bounded_packed_q_interval_valid_cv_symmetric_half:
  bounded_object_q_nonnegative error ==>
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_symmetric_half_interval_cv error)
Proof
  strip_tac
  >> Cases_on `bounded_object_q_ints error`
  >- fs
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_nonnegative_def]
  >> PairCases_on `x`
  >> `0 < x1 /\ 0 <= x0` by
       fs
         [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_nonnegative_def]
  >> `bounded_object_q_interval_ints
        (bounded_object_q_symmetric_half_interval_cv error) =
      SOME ((-x0,x1 * (&2:int)),(x0,x1 * (&2:int)))` by
       (irule
          compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_decodes
        >> simp [])
  >> `0 < x1 * (&2:int) /\ 0 < x1 * (&2:int) /\
      (-x0) * (x1 * (&2:int)) <= x0 * (x1 * (&2:int))` by
       metis_tac
         [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_ordered]
  >> rw
       [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_packed_q_interval_valid_cv_taylor_value_complete:
  bounded_packed_q_interval_valid_cv center /\
  bounded_object_q_nonnegative error ==>
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_taylor_value_complete_cv center error)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def]
  >> irule
       compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add
  >> simp [bounded_packed_q_interval_valid_cv_symmetric_half]
QED

Theorem bounded_packed_q_interval_valid_cv_taylor_gradient_row_complete:
  LENGTH radii = LENGTH hessian_row /\
  bounded_packed_q_interval_valid_cv center_entry /\
  EVERY bounded_packed_q_interval_valid_cv hessian_row ==>
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_taylor_gradient_row_complete_cv center_entry
      (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
        (bounded_word64_object_q_cv 0w)))
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_row_complete_cv_def]
  >> irule bounded_packed_q_interval_valid_cv_taylor_value_complete
  >> simp []
  >> irule
       compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_add_cv_nonnegative
  >> metis_tac
       [bounded_object_q_dot_abs_upper_acc_cv_nonnegative_valid,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_word64_object_q_cv_nonnegative]
QED

Theorem bounded_object_q_taylor_gradient_rows_complete_cv_valid:
  !center_gradient rows.
    LENGTH center_gradient = LENGTH rows /\
    EVERY bounded_packed_q_interval_valid_cv center_gradient /\
    EVERY
      (\row.
        LENGTH row = LENGTH radii /\
        EVERY bounded_packed_q_interval_valid_cv row) rows ==>
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_object_q_taylor_gradient_rows_complete_cv
        radii center_gradient rows)
Proof
  Induct
  >> Cases_on `rows`
  >> simp
       [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_rows_complete_cv_def]
  >> metis_tac
       [bounded_packed_q_interval_valid_cv_taylor_gradient_row_complete]
QED

Theorem bounded_hessian64_rows_valid:
  bounded_hessian64_rows hessian = SOME rows /\
  EVERY bounded_packed_q_interval_valid_cv hessian ==>
  LENGTH rows = 6 /\
  EVERY
    (\row.
      LENGTH row = 6 /\
      EVERY bounded_packed_q_interval_valid_cv row) rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_object_q_taylor_gradient_complete_cv_valid:
  LENGTH radii = 6 /\
  LENGTH center_gradient = 6 /\
  LENGTH hessian = 21 /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv hessian ==>
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_taylor_gradient_complete_cv
      radii center_gradient hessian)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_complete_cv_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_hessian64_rows_valid
  >> irule bounded_object_q_taylor_gradient_rows_complete_cv_valid
  >> simp []
QED

Theorem bounded_object_q_taylor_recomplete_semantic_valid:
  LENGTH radii = 6 /\
  LENGTH weights = 21 /\
  bounded_packed_q_interval_valid_cv center /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_object_q_taylor_semantic_valid
    (BoundedObjectQTaylor domain_flag center center_gradient
      (bounded_object_q_taylor_value_complete_cv center
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian))
      (bounded_object_q_taylor_gradient_complete_cv
        radii center_gradient hessian)
      hessian)
Proof
  strip_tac
  >> simp [bounded_object_q_taylor_semantic_valid_def]
  >> rpt conj_tac
  >- (irule bounded_packed_q_interval_valid_cv_taylor_value_complete
      >> simp []
      >> irule bounded_object_q_taylor_error_cv_nonnegative_valid
      >> simp [])
  >- (irule bounded_object_q_taylor_gradient_complete_cv_valid
      >> simp [])
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_taylor_gradient_complete_cv_length6
  >> simp []
QED

Theorem bounded_object_q_taylor_neg_semantic_valid:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_object_q_taylor_semantic_valid semantic_state ==>
  bounded_object_q_taylor_semantic_valid
    (bounded_object_q_taylor_neg radii weights semantic_state)
Proof
  Cases_on `semantic_state`
  >> strip_tac
  >> fs [bounded_object_q_taylor_semantic_valid_def]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
        LET_THM]
  >> simp [LET_THM]
  >> irule bounded_object_q_taylor_recomplete_semantic_valid
  >> simp
       [compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_neg,
        compute_boundedCase16594ObjectNegRelationTheory.bounded_packed_q_interval_valid_cv_map_neg]
QED

Theorem bounded_object_q_taylor_add_semantic_valid:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_object_q_taylor_semantic_valid left /\
  bounded_object_q_taylor_semantic_valid right ==>
  bounded_object_q_taylor_semantic_valid
    (bounded_object_q_taylor_add radii weights left right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> strip_tac
  >> fs [bounded_object_q_taylor_semantic_valid_def]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
        LET_THM]
  >> simp [LET_THM]
  >> irule bounded_object_q_taylor_recomplete_semantic_valid
  >> simp []
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add
      >> simp [])
  >- (irule
        compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_valid
      >> simp [])
  >> irule
       compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_valid
  >> simp []
QED

Theorem bounded_object_q_taylor_mul_semantic_valid:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_object_q_taylor_semantic_valid left /\
  bounded_object_q_taylor_semantic_valid right ==>
  bounded_object_q_taylor_semantic_valid
    (bounded_object_q_taylor_mul radii weights left right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> strip_tac
  >> fs [bounded_object_q_taylor_semantic_valid_def]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        LET_THM]
  >> simp [LET_THM]
  >> irule bounded_object_q_taylor_recomplete_semantic_valid
  >> simp []
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul
      >> simp [])
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_fused_scale_add_cv_length6_relation
      >> simp [])
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_fused_hessian_cv_length21_relation
      >> simp
        [compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_symmetric_product_pairs_cv_length6_relation])
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_fused_scale_add
      >> simp [])
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_fused_hessian_cv_valid
      >> simp []
      >> irule
           compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_symmetric_product_pairs_cv_valid
      >> simp [])
QED

Theorem bounded_case16594_object_poly_step_square_control_eval:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instruction»,from_cv (Num 5));
         («stack»,from_cv (Pair operand rest))]
        bounded_case16594_object_poly_step_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (Pair (Num 1)
        (Pair
          (App «candle_cv_q_packed_object_state_mul»
            [from_cv radii;from_cv operand;from_cv operand])
          (from_cv rest))) refs
Proof
  simp
    [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_poly_step_square_eval_from_state:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_mul»
        [from_cv radii;from_cv operand;from_cv operand])
      (refs:hol_refs) = (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 5);from_cv (Pair operand rest)]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair result_state rest))),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_unfold]
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_poly_step_square_control_eval]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> asm_simp_tac std_ss [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_poly_step_neg_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines runtime_state semantic_state /\
  4102 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (compute_exec$Num 2);
         from_cv (Pair runtime_state rest)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1) (Pair result_state rest))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_neg semantic_radii weights semantic_state)
Proof
  Cases_on `semantic_state`
  >> strip_tac
  >> `bounded_object_q_taylor_semantic_valid
        (BoundedObjectQTaylor b c l c0 l0 l1)` by
       fs [bounded_object_q_taylor_runtime_refines_def]
  >> drule bounded_object_q_taylor_runtime_refines_contract
  >> disch_then
       (qx_choose_then `runtime_center`
         (qx_choose_then `runtime_center_gradient`
           (qx_choose_then `runtime_value_bound`
             (qx_choose_then `runtime_gradient_bounds`
               (qx_choose_then `runtime_hessian` strip_assume_tac)))))
  >> gvs []
  >> mp_tac
       (Q.INST
         [`semantic_center` |-> `c`,
          `semantic_center_gradient` |-> `l`,
          `semantic_value` |-> `c0`,
          `semantic_gradient_bounds` |-> `l0`,
          `semantic_hessian` |-> `l1`]
         (INST
           [mk_var ("runtime_gradient_bounds",``:cv``) |->
              ``bounded_object_q_cv_list runtime_gradient_bounds``]
           (Q.INST [`runtime_value` |-> `runtime_value_bound`]
             (Q.SPEC `b`
               compute_boundedCase16594ObjectPolyBaseStepSemanticEvalTheory.bounded_case16594_object_poly_step_neg_eval_semantic))))
  >> impl_tac
  >- fs [bounded_object_q_taylor_semantic_valid_def]
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> fs [compute_execTheory.from_cv_def]
  >> rw [bounded_object_q_taylor_runtime_refines_def]
  >> irule bounded_object_q_taylor_neg_semantic_valid
  >> simp []
QED

Theorem bounded_case16594_object_poly_step_add_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines
    runtime_left_state semantic_left_state /\
  bounded_object_q_taylor_runtime_refines
    runtime_right_state semantic_right_state /\
  4102 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (compute_exec$Num 3);
         from_cv
           (Pair runtime_right_state
             (Pair runtime_left_state rest))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1) (Pair result_state rest))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_add semantic_radii weights
        semantic_left_state semantic_right_state)
Proof
  Cases_on `semantic_left_state`
  >> Cases_on `semantic_right_state`
  >> strip_tac
  >> `bounded_object_q_taylor_semantic_valid
        (BoundedObjectQTaylor b c l c0 l0 l1) /\
      bounded_object_q_taylor_semantic_valid
        (BoundedObjectQTaylor b' c' l' c0' l0' l1')` by
       fs [bounded_object_q_taylor_runtime_refines_def]
  >> qpat_x_assum
       `bounded_object_q_taylor_runtime_refines runtime_left_state
          (BoundedObjectQTaylor b c l c0 l0 l1)`
       (fn th =>
         mp_tac
           (MATCH_MP bounded_object_q_taylor_runtime_refines_contract th))
  >> disch_then
       (qx_choose_then `runtime_left_center`
         (qx_choose_then `runtime_left_center_gradient`
           (qx_choose_then `runtime_left_value_bound`
             (qx_choose_then `runtime_left_gradient_bounds`
               (qx_choose_then `runtime_left_hessian`
                 strip_assume_tac)))))
  >> qpat_x_assum
       `bounded_object_q_taylor_runtime_refines runtime_right_state
          (BoundedObjectQTaylor b' c' l' c0' l0' l1')`
       (fn th =>
         mp_tac
           (MATCH_MP bounded_object_q_taylor_runtime_refines_contract th))
  >> disch_then
       (qx_choose_then `runtime_right_center`
         (qx_choose_then `runtime_right_center_gradient`
           (qx_choose_then `runtime_right_value_bound`
             (qx_choose_then `runtime_right_gradient_bounds`
               (qx_choose_then `runtime_right_hessian`
                 strip_assume_tac)))))
  >> gvs []
  >> mp_tac
       (Q.INST
         [`runtime_left_value` |-> `runtime_left_value_bound`,
          `runtime_right_value` |-> `runtime_right_value_bound`,
          `semantic_left_center` |-> `c`,
          `semantic_left_center_gradient` |-> `l`,
          `semantic_left_value` |-> `c0`,
          `semantic_left_gradient_bounds` |-> `l0`,
          `semantic_left_hessian` |-> `l1`,
          `semantic_right_center` |-> `c'`,
          `semantic_right_center_gradient` |-> `l'`,
          `semantic_right_value` |-> `c0'`,
          `semantic_right_gradient_bounds` |-> `l0'`,
          `semantic_right_hessian` |-> `l1'`]
         (Q.SPECL [`b`,`b'`]
           compute_boundedCase16594ObjectPolyAddStepSemanticEvalTheory.bounded_case16594_object_poly_step_add_eval_semantic))
  >> impl_tac
  >- fs [bounded_object_q_taylor_semantic_valid_def]
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> fs [compute_execTheory.from_cv_def]
  >> rw [bounded_object_q_taylor_runtime_refines_def]
  >> irule bounded_object_q_taylor_add_semantic_valid
  >> simp []
QED

Theorem bounded_case16594_object_poly_step_mul_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines
    runtime_left_state semantic_left_state /\
  bounded_object_q_taylor_runtime_refines
    runtime_right_state semantic_right_state /\
  4102 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (compute_exec$Num 4);
         from_cv
           (Pair runtime_right_state
             (Pair runtime_left_state rest))]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1) (Pair result_state rest))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_mul semantic_radii weights
        semantic_left_state semantic_right_state)
Proof
  Cases_on `semantic_left_state`
  >> Cases_on `semantic_right_state`
  >> strip_tac
  >> `bounded_object_q_taylor_semantic_valid
        (BoundedObjectQTaylor b c l c0 l0 l1) /\
      bounded_object_q_taylor_semantic_valid
        (BoundedObjectQTaylor b' c' l' c0' l0' l1')` by
       fs [bounded_object_q_taylor_runtime_refines_def]
  >> qpat_x_assum
       `bounded_object_q_taylor_runtime_refines runtime_left_state
          (BoundedObjectQTaylor b c l c0 l0 l1)`
       (fn th =>
         mp_tac
           (MATCH_MP bounded_object_q_taylor_runtime_refines_contract th))
  >> disch_then
       (qx_choose_then `runtime_left_center`
         (qx_choose_then `runtime_left_center_gradient`
           (qx_choose_then `runtime_left_value_bound`
             (qx_choose_then `runtime_left_gradient_bounds`
               (qx_choose_then `runtime_left_hessian`
                 strip_assume_tac)))))
  >> qpat_x_assum
       `bounded_object_q_taylor_runtime_refines runtime_right_state
          (BoundedObjectQTaylor b' c' l' c0' l0' l1')`
       (fn th =>
         mp_tac
           (MATCH_MP bounded_object_q_taylor_runtime_refines_contract th))
  >> disch_then
       (qx_choose_then `runtime_right_center`
         (qx_choose_then `runtime_right_center_gradient`
           (qx_choose_then `runtime_right_value_bound`
             (qx_choose_then `runtime_right_gradient_bounds`
               (qx_choose_then `runtime_right_hessian`
                 strip_assume_tac)))))
  >> gvs []
  >> mp_tac
       (Q.INST
         [`runtime_left_value` |-> `runtime_left_value_bound`,
          `runtime_right_value` |-> `runtime_right_value_bound`,
          `semantic_left_center` |-> `c`,
          `semantic_left_center_gradient` |-> `l`,
          `semantic_left_value` |-> `c0`,
          `semantic_left_gradient_bounds` |-> `l0`,
          `semantic_left_hessian` |-> `l1`,
          `semantic_right_center` |-> `c'`,
          `semantic_right_center_gradient` |-> `l'`,
          `semantic_right_value` |-> `c0'`,
          `semantic_right_gradient_bounds` |-> `l0'`,
          `semantic_right_hessian` |-> `l1'`]
         (Q.SPECL [`b`,`b'`]
           compute_boundedCase16594ObjectPolyMulStepSemanticEvalTheory.bounded_case16594_object_poly_step_mul_eval_semantic))
  >> impl_tac
  >- fs [bounded_object_q_taylor_semantic_valid_def]
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> fs [compute_execTheory.from_cv_def]
  >> rw [bounded_object_q_taylor_runtime_refines_def]
  >> irule bounded_object_q_taylor_mul_semantic_valid
  >> simp []
QED

Theorem bounded_case16594_object_poly_step_square_eval_runtime_refines:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_taylor_runtime_refines runtime_state semantic_state /\
  4102 < clock ==>
  ?result_state.
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;
         from_cv (bounded_object_q_cv_list runtime_radii);
         from_cv (compute_exec$Num 5);
         from_cv (Pair runtime_state rest)]) (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (compute_exec$Num 1) (Pair result_state rest))),refs) /\
    bounded_object_q_taylor_runtime_refines result_state
      (bounded_object_q_taylor_mul semantic_radii weights
        semantic_state semantic_state)
Proof
  Cases_on `semantic_state`
  >> strip_tac
  >> `bounded_object_q_taylor_semantic_valid
        (BoundedObjectQTaylor b c l c0 l0 l1)` by
       fs [bounded_object_q_taylor_runtime_refines_def]
  >> drule bounded_object_q_taylor_runtime_refines_contract
  >> disch_then
       (qx_choose_then `runtime_center`
         (qx_choose_then `runtime_center_gradient`
           (qx_choose_then `runtime_value_bound`
             (qx_choose_then `runtime_gradient_bounds`
               (qx_choose_then `runtime_hessian` strip_assume_tac)))))
  >> gvs []
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`,
          `runtime_left_center` |-> `runtime_center`,
          `runtime_left_center_gradient` |-> `runtime_center_gradient`,
          `runtime_left_value` |-> `runtime_value_bound`,
          `runtime_left_gradient_bounds` |-> `runtime_gradient_bounds`,
          `runtime_left_hessian` |-> `runtime_hessian`,
          `runtime_right_center` |-> `runtime_center`,
          `runtime_right_center_gradient` |-> `runtime_center_gradient`,
          `runtime_right_value` |-> `runtime_value_bound`,
          `runtime_right_gradient_bounds` |-> `runtime_gradient_bounds`,
          `runtime_right_hessian` |-> `runtime_hessian`,
          `semantic_left_center` |-> `c`,
          `semantic_left_center_gradient` |-> `l`,
          `semantic_left_value` |-> `c0`,
          `semantic_left_gradient_bounds` |-> `l0`,
          `semantic_left_hessian` |-> `l1`,
          `semantic_right_center` |-> `c`,
          `semantic_right_center_gradient` |-> `l`,
          `semantic_right_value` |-> `c0`,
          `semantic_right_gradient_bounds` |-> `l0`,
          `semantic_right_hessian` |-> `l1`]
         (Q.SPECL [`b`,`b`]
           compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_state_mul_eval_semantic))
  >> impl_tac
  >- (fs [bounded_object_q_taylor_semantic_valid_def]
      >> intLib.ARITH_TAC)
  >> disch_then (qx_choose_then `result_state` strip_assume_tac)
  >> qexists_tac `result_state`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_poly_step_square_eval_from_state)
      >> simp []
      >> intLib.ARITH_TAC)
  >> rw [bounded_object_q_taylor_runtime_refines_def]
  >> irule bounded_object_q_taylor_mul_semantic_valid
  >> simp []
QED

val _ = export_theory ();
