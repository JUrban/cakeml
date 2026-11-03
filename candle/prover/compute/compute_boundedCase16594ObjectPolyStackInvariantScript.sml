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

val _ = export_theory ();
