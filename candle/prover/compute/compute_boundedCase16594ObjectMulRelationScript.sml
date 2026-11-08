(*****************************************************************************
 * Representation-independent multiplication relations for the production
 * object checker.  This is the algebraic half of the generic state-multiply
 * bridge: runtime rationals may use different numerators/denominators, but
 * every constructed interval denotes the same mathematical enclosure.
 *****************************************************************************)
open compute_boundedCase16594ObjectRecompleteRelationTheory
open compute_boundedCase16594ObjectRuntimePreservationTheory
open compute_boundedObjectTaylorEquivalenceTheory
open preamble

Theory compute_boundedCase16594ObjectMulRelation
Ancestors
  compute_boundedCase16594ObjectRecompleteRelation
Libs
  bossLib preamble intLib

Theorem bounded_object_q_min_cv_equiv_cong:
  bounded_case10173_q_cv_equiv left left' /\
  bounded_case10173_q_cv_equiv right right' ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_min_cv left right)
    (bounded_object_q_min_cv left' right')
Proof
  strip_tac
  >> `bounded_object_q_le_cv left right =
      bounded_object_q_le_cv left' right'` by
       metis_tac [bounded_object_q_le_cv_equiv_cong]
  >> rw
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min_cv_def]
  >> every_case_tac
  >> fs []
QED

Theorem bounded_object_q_min4_cv_equiv_cong:
  bounded_case10173_q_cv_equiv first_cv first_cv' /\
  bounded_case10173_q_cv_equiv second_cv second_cv' /\
  bounded_case10173_q_cv_equiv third_cv third_cv' /\
  bounded_case10173_q_cv_equiv fourth_cv fourth_cv' ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_min4_cv first_cv second_cv third_cv fourth_cv)
    (bounded_object_q_min4_cv first_cv' second_cv' third_cv' fourth_cv')
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_min4_cv_def]
  >> irule bounded_object_q_min_cv_equiv_cong
  >> conj_tac
  >> irule bounded_object_q_min_cv_equiv_cong
  >> simp []
QED

Theorem bounded_object_q_max4_cv_equiv_cong:
  bounded_case10173_q_cv_equiv first_cv first_cv' /\
  bounded_case10173_q_cv_equiv second_cv second_cv' /\
  bounded_case10173_q_cv_equiv third_cv third_cv' /\
  bounded_case10173_q_cv_equiv fourth_cv fourth_cv' ==>
  bounded_case10173_q_cv_equiv
    (bounded_object_q_max4_cv first_cv second_cv third_cv fourth_cv)
    (bounded_object_q_max4_cv first_cv' second_cv' third_cv' fourth_cv')
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_max4_cv_def]
  >> irule bounded_object_q_max_cv_equiv_cong
  >> conj_tac
  >> irule bounded_object_q_max_cv_equiv_cong
  >> simp []
QED

Theorem bounded_object_q_interval_mul_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv left left' /\
  bounded_object_q_interval_cv_equiv right right' ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_mul_cv left right)
    (bounded_object_q_interval_mul_cv left' right')
Proof
  Cases_on `left`
  >> Cases_on `left'`
  >> Cases_on `right`
  >> Cases_on `right'`
  >> simp
       [bounded_object_q_interval_cv_equiv_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_def,
        LET_THM]
  >> strip_tac
  >> conj_tac
  >- (irule bounded_object_q_min4_cv_equiv_cong
      >> rpt conj_tac
      >> irule
           compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
      >> simp [])
  >> irule bounded_object_q_max4_cv_equiv_cong
  >> rpt conj_tac
  >> irule
       compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
  >> simp []
QED

Theorem bounded_packed_q_interval_valid_cv_mul:
  bounded_packed_q_interval_valid_cv left /\
  bounded_packed_q_interval_valid_cv right ==>
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_mul_cv left right)
Proof
  rw
       [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> qexists_tac
       `bounded_object_q_interval_mul_ints decoded decoded'`
  >> conj_tac
  >- (irule
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_interval_mul_cv_decodes
      >> simp [])
  >> metis_tac
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_mul_ints_valid]
QED

Theorem bounded_object_q_interval_add_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv left left' /\
  bounded_object_q_interval_cv_equiv right right' ==>
  bounded_object_q_interval_cv_equiv
    (bounded_object_q_interval_add_cv left right)
    (bounded_object_q_interval_add_cv left' right')
Proof
  Cases_on `left`
  >> Cases_on `left'`
  >> Cases_on `right`
  >> Cases_on `right'`
  >> simp
       [bounded_object_q_interval_cv_equiv_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong]
QED

Theorem bounded_packed_q_interval_valid_cv_add:
  bounded_packed_q_interval_valid_cv left /\
  bounded_packed_q_interval_valid_cv right ==>
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_add_cv left right)
Proof
  rw
       [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> qexists_tac `bounded_object_q_interval_add_ints decoded decoded'`
  >> conj_tac
  >- (irule
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_decodes
      >> simp [])
  >> metis_tac
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_add_ints_valid]
QED

Definition bounded_object_q_interval_product_pair_equiv_def:
  bounded_object_q_interval_product_pair_equiv runtime semantic <=>
    bounded_object_q_interval_cv_equiv (FST runtime) (FST semantic) /\
    bounded_object_q_interval_cv_equiv (SND runtime) (SND semantic)
End

Theorem bounded_object_q_interval_products_sum_acc_cv_rel:
  !runtime_inputs semantic_inputs runtime_acc semantic_acc.
    LIST_REL bounded_object_q_interval_product_pair_equiv
      runtime_inputs semantic_inputs /\
    bounded_object_q_interval_cv_equiv runtime_acc semantic_acc ==>
    bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_products_sum_acc_cv
        runtime_inputs runtime_acc)
      (bounded_object_q_interval_products_sum_acc_cv
        semantic_inputs semantic_acc)
Proof
  Induct
  >> Cases_on `semantic_inputs`
  >> simp
       [LIST_REL_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> rpt gen_tac
  >> Cases_on `h`
  >> Cases_on `h'`
  >> simp [bounded_object_q_interval_product_pair_equiv_def]
  >> metis_tac
       [bounded_object_q_interval_add_cv_equiv_cong,
        bounded_object_q_interval_mul_cv_equiv_cong]
QED

Theorem bounded_packed_q_interval_valid_cv_products_sum_acc:
  !inputs accumulator.
    EVERY
      (\input.
        bounded_packed_q_interval_valid_cv (FST input) /\
        bounded_packed_q_interval_valid_cv (SND input)) inputs /\
    bounded_packed_q_interval_valid_cv accumulator ==>
    bounded_packed_q_interval_valid_cv
      (bounded_object_q_interval_products_sum_acc_cv inputs accumulator)
Proof
  Induct
  >- simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> Cases_on `h`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_products_sum_acc_cv_def]
  >> metis_tac
       [bounded_packed_q_interval_valid_cv_add,
        bounded_packed_q_interval_valid_cv_mul]
QED

Theorem bounded_packed_q_interval_valid_cv_zero:
  bounded_packed_q_interval_valid_cv
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  simp
       [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_analytic_source_q_zero_interval_cv_decodes,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

Theorem bounded_object_q_interval_zero_equiv_refl:
  bounded_object_q_interval_cv_equiv
    (bounded_analytic_source_q_interval_cv 0 0 0)
    (bounded_analytic_source_q_interval_cv 0 0 0)
Proof
  irule bounded_object_q_interval_cv_equiv_refl
  >> metis_tac
       [bounded_packed_q_interval_valid_cv_zero,
        bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_object_q_interval_fused_scale_add_cv_rel:
  !runtime_left semantic_left runtime_right semantic_right.
    bounded_object_q_interval_cv_equiv
      runtime_left_scale semantic_left_scale /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_left semantic_left /\
    bounded_object_q_interval_cv_equiv
      runtime_right_scale semantic_right_scale /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_right semantic_right ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_fused_scale_add_cv
        runtime_left_scale runtime_left runtime_right_scale runtime_right)
      (bounded_object_q_interval_fused_scale_add_cv
        semantic_left_scale semantic_left semantic_right_scale semantic_right)
Proof
  Induct
  >> Cases_on `semantic_left`
  >> Cases_on `runtime_right`
  >> Cases_on `semantic_right`
  >> simp
       [LIST_REL_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def,
        bounded_object_q_interval_product_pair_equiv_def]
  >> rpt strip_tac
  >> irule bounded_object_q_interval_products_sum_acc_cv_rel
  >> simp
       [LIST_REL_def,
        bounded_object_q_interval_product_pair_equiv_def,
        bounded_object_q_interval_zero_equiv_refl]
QED

Theorem bounded_packed_q_interval_valid_cv_fused_scale_add:
  !left right.
    bounded_packed_q_interval_valid_cv left_scale /\
    EVERY bounded_packed_q_interval_valid_cv left /\
    bounded_packed_q_interval_valid_cv right_scale /\
    EVERY bounded_packed_q_interval_valid_cv right ==>
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_object_q_interval_fused_scale_add_cv
        left_scale left right_scale right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
  >> rpt strip_tac
  >> irule bounded_packed_q_interval_valid_cv_products_sum_acc
  >> simp [bounded_packed_q_interval_valid_cv_zero]
QED

Definition bounded_object_q_symmetric_pair_equiv_def:
  bounded_object_q_symmetric_pair_equiv runtime semantic <=>
    bounded_object_q_interval_product_pair_equiv
      (FST runtime) (FST semantic) /\
    bounded_object_q_interval_product_pair_equiv
      (SND runtime) (SND semantic)
End

Theorem bounded_object_q_symmetric_product_pairs_row_cv_rel:
  !runtime_left semantic_left runtime_right semantic_right.
    bounded_object_q_interval_cv_equiv
      runtime_fixed_left semantic_fixed_left /\
    bounded_object_q_interval_cv_equiv
      runtime_fixed_right semantic_fixed_right /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_left semantic_left /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_right semantic_right ==>
    LIST_REL bounded_object_q_symmetric_pair_equiv
      (bounded_object_q_symmetric_product_pairs_row_cv
        runtime_fixed_left runtime_fixed_right runtime_left runtime_right)
      (bounded_object_q_symmetric_product_pairs_row_cv
        semantic_fixed_left semantic_fixed_right semantic_left semantic_right)
Proof
  Induct
  >> Cases_on `semantic_left`
  >> Cases_on `runtime_right`
  >> Cases_on `semantic_right`
  >> simp
       [LIST_REL_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def,
        bounded_object_q_symmetric_pair_equiv_def,
        bounded_object_q_interval_product_pair_equiv_def]
QED

Theorem bounded_object_q_symmetric_product_pairs_cv_rel:
  !runtime_left semantic_left runtime_right semantic_right.
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_left semantic_left /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_right semantic_right ==>
    LIST_REL bounded_object_q_symmetric_pair_equiv
      (bounded_object_q_symmetric_product_pairs_cv
        runtime_left runtime_right)
      (bounded_object_q_symmetric_product_pairs_cv
        semantic_left semantic_right)
Proof
  Induct
  >> Cases_on `semantic_left`
  >> Cases_on `runtime_right`
  >> Cases_on `semantic_right`
  >> simp
       [LIST_REL_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def]
  >> rpt strip_tac
  >> irule listTheory.LIST_REL_APPEND_suff
  >> conj_tac
  >- (irule bounded_object_q_symmetric_product_pairs_row_cv_rel
      >> simp [LIST_REL_def])
  >> first_x_assum irule
  >> simp []
QED

Definition bounded_object_q_interval_product_pair_valid_def:
  bounded_object_q_interval_product_pair_valid pair <=>
    bounded_packed_q_interval_valid_cv (FST pair) /\
    bounded_packed_q_interval_valid_cv (SND pair)
End

Definition bounded_object_q_symmetric_pair_valid_def:
  bounded_object_q_symmetric_pair_valid outer <=>
    bounded_object_q_interval_product_pair_valid (FST outer) /\
    bounded_object_q_interval_product_pair_valid (SND outer)
End

Theorem bounded_packed_q_symmetric_product_pairs_row_cv_valid:
  !left right.
    bounded_packed_q_interval_valid_cv fixed_left /\
    bounded_packed_q_interval_valid_cv fixed_right /\
    EVERY bounded_packed_q_interval_valid_cv left /\
    EVERY bounded_packed_q_interval_valid_cv right ==>
    EVERY bounded_object_q_symmetric_pair_valid
      (bounded_object_q_symmetric_product_pairs_row_cv
        fixed_left fixed_right left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def,
        bounded_object_q_symmetric_pair_valid_def,
        bounded_object_q_interval_product_pair_valid_def]
QED

Theorem bounded_packed_q_symmetric_product_pairs_cv_valid:
  !left right.
    EVERY bounded_packed_q_interval_valid_cv left /\
    EVERY bounded_packed_q_interval_valid_cv right ==>
    EVERY bounded_object_q_symmetric_pair_valid
      (bounded_object_q_symmetric_product_pairs_cv left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def]
  >> rpt strip_tac
  >> irule bounded_packed_q_symmetric_product_pairs_row_cv_valid
  >> simp []
QED

Theorem bounded_object_q_interval_fused_hessian_cv_rel:
  !runtime_left_hessian semantic_left_hessian
    runtime_right_hessian semantic_right_hessian
    runtime_outer semantic_outer.
    bounded_object_q_interval_cv_equiv
      runtime_left_value semantic_left_value /\
    bounded_object_q_interval_cv_equiv
      runtime_right_value semantic_right_value /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_left_hessian semantic_left_hessian /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_right_hessian semantic_right_hessian /\
    LIST_REL bounded_object_q_symmetric_pair_equiv
      runtime_outer semantic_outer ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_fused_hessian_cv
        runtime_left_value runtime_right_value
        runtime_left_hessian runtime_right_hessian runtime_outer)
      (bounded_object_q_interval_fused_hessian_cv
        semantic_left_value semantic_right_value
        semantic_left_hessian semantic_right_hessian semantic_outer)
Proof
  Induct
  >> Cases_on `semantic_left_hessian`
  >> Cases_on `runtime_right_hessian`
  >> Cases_on `semantic_right_hessian`
  >> Cases_on `runtime_outer`
  >> Cases_on `semantic_outer`
  >> simp
       [LIST_REL_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def,
        bounded_object_q_symmetric_pair_equiv_def]
  >> rpt strip_tac
  >> irule bounded_object_q_interval_products_sum_acc_cv_rel
  >> simp
       [LIST_REL_def,
        bounded_object_q_symmetric_pair_equiv_def,
        bounded_object_q_interval_product_pair_equiv_def,
        bounded_object_q_interval_zero_equiv_refl]
QED

Theorem bounded_packed_q_interval_fused_hessian_cv_valid:
  !left_hessian right_hessian outer.
    bounded_packed_q_interval_valid_cv left_value /\
    bounded_packed_q_interval_valid_cv right_value /\
    EVERY bounded_packed_q_interval_valid_cv left_hessian /\
    EVERY bounded_packed_q_interval_valid_cv right_hessian /\
    EVERY bounded_object_q_symmetric_pair_valid outer ==>
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_object_q_interval_fused_hessian_cv
        left_value right_value left_hessian right_hessian outer)
Proof
  Induct
  >> Cases_on `right_hessian`
  >> Cases_on `outer`
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def,
        bounded_object_q_symmetric_pair_valid_def]
  >> rpt strip_tac
  >> irule bounded_packed_q_interval_valid_cv_products_sum_acc
  >> fs
       [bounded_object_q_interval_product_pair_valid_def,
        bounded_packed_q_interval_valid_cv_zero]
QED

Theorem bounded_object_q_symmetric_product_pairs_cv_length6_relation:
  LENGTH left = 6 /\
  LENGTH right = 6 ==>
  LENGTH (bounded_object_q_symmetric_product_pairs_cv left right) = 21
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_cv_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_symmetric_product_pairs_row_cv_def]
QED

Theorem bounded_object_q_interval_fused_scale_add_cv_length6_relation:
  LENGTH left = 6 /\
  LENGTH right = 6 ==>
  LENGTH
    (bounded_object_q_interval_fused_scale_add_cv
      left_scale left right_scale right) = 6
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_scale_add_cv_def]
QED

Theorem bounded_object_q_interval_fused_hessian_cv_length21_relation:
  LENGTH left_hessian = 21 /\
  LENGTH right_hessian = 21 /\
  LENGTH outer = 21 ==>
  LENGTH
    (bounded_object_q_interval_fused_hessian_cv
      left_value right_value left_hessian right_hessian outer) = 21
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> simp
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_object_q_interval_fused_hessian_cv_def]
QED

Theorem bounded_case16594_object_mul_recomplete_runtime_semantic_equiv:
  !left_domain right_domain.
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_interval_cv_equiv
    runtime_left_center semantic_left_center /\
  bounded_packed_q_interval_valid_cv semantic_left_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_left_center_gradient semantic_left_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_left_center_gradient /\
  LENGTH semantic_left_center_gradient = 6 /\
  bounded_object_q_interval_cv_equiv
    runtime_left_value semantic_left_value /\
  bounded_packed_q_interval_valid_cv semantic_left_value /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_left_gradient_bounds semantic_left_gradient_bounds /\
  EVERY bounded_packed_q_interval_valid_cv semantic_left_gradient_bounds /\
  LENGTH semantic_left_gradient_bounds = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_left_hessian semantic_left_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_left_hessian /\
  LENGTH semantic_left_hessian = 21 /\
  bounded_object_q_interval_cv_equiv
    runtime_right_center semantic_right_center /\
  bounded_packed_q_interval_valid_cv semantic_right_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_center_gradient semantic_right_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_center_gradient /\
  LENGTH semantic_right_center_gradient = 6 /\
  bounded_object_q_interval_cv_equiv
    runtime_right_value semantic_right_value /\
  bounded_packed_q_interval_valid_cv semantic_right_value /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_gradient_bounds semantic_right_gradient_bounds /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_gradient_bounds /\
  LENGTH semantic_right_gradient_bounds = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_hessian semantic_right_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_hessian /\
  LENGTH semantic_right_hessian = 21 ==>
  bounded_object_q_taylor_runtime_equiv
    (let runtime_center =
           bounded_object_q_interval_mul_cv
             runtime_left_center runtime_right_center;
         runtime_center_gradient =
           bounded_object_q_interval_fused_scale_add_cv
             runtime_right_center runtime_left_center_gradient
             runtime_left_center runtime_right_center_gradient;
         runtime_outer =
           bounded_object_q_symmetric_product_pairs_cv
             runtime_left_gradient_bounds runtime_right_gradient_bounds;
         runtime_hessian =
           bounded_object_q_interval_fused_hessian_cv
             runtime_left_value runtime_right_value
             runtime_left_hessian runtime_right_hessian runtime_outer
     in
       bounded_case16594_object_state_cv
         (if left_domain /\ right_domain then Num 1 else Num 0)
         runtime_center
         (bounded_object_q_cv_list runtime_center_gradient)
         (bounded_packed_q_source_value_bound6_cv runtime_radii
           runtime_center runtime_center_gradient runtime_hessian)
         (bounded_object_q_cv_list
           (bounded_packed_q_source_gradient_complete6_cv runtime_radii
             runtime_center_gradient runtime_hessian))
         (bounded_object_q_cv_list runtime_hessian))
    (bounded_object_q_taylor_mul semantic_radii weights
      (BoundedObjectQTaylor left_domain semantic_left_center
        semantic_left_center_gradient semantic_left_value
        semantic_left_gradient_bounds semantic_left_hessian)
      (BoundedObjectQTaylor right_domain semantic_right_center
        semantic_right_center_gradient semantic_right_value
        semantic_right_gradient_bounds semantic_right_hessian))
Proof
  rpt gen_tac
  >> strip_tac
  >> `bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_mul_cv
          runtime_left_center runtime_right_center)
        (bounded_object_q_interval_mul_cv
          semantic_left_center semantic_right_center)` by
       metis_tac [bounded_object_q_interval_mul_cv_equiv_cong]
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_mul_cv
          semantic_left_center semantic_right_center)` by
       metis_tac [bounded_packed_q_interval_valid_cv_mul]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_fused_scale_add_cv
          runtime_right_center runtime_left_center_gradient
          runtime_left_center runtime_right_center_gradient)
        (bounded_object_q_interval_fused_scale_add_cv
          semantic_right_center semantic_left_center_gradient
          semantic_left_center semantic_right_center_gradient)` by
       metis_tac [bounded_object_q_interval_fused_scale_add_cv_rel]
  >> `EVERY bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_fused_scale_add_cv
          semantic_right_center semantic_left_center_gradient
          semantic_left_center semantic_right_center_gradient)` by
       metis_tac [bounded_packed_q_interval_valid_cv_fused_scale_add]
  >> `LENGTH
        (bounded_object_q_interval_fused_scale_add_cv
          semantic_right_center semantic_left_center_gradient
          semantic_left_center semantic_right_center_gradient) = 6` by
       metis_tac
         [bounded_object_q_interval_fused_scale_add_cv_length6_relation]
  >> `LIST_REL bounded_object_q_symmetric_pair_equiv
        (bounded_object_q_symmetric_product_pairs_cv
          runtime_left_gradient_bounds runtime_right_gradient_bounds)
        (bounded_object_q_symmetric_product_pairs_cv
          semantic_left_gradient_bounds semantic_right_gradient_bounds)` by
       metis_tac [bounded_object_q_symmetric_product_pairs_cv_rel]
  >> `EVERY bounded_object_q_symmetric_pair_valid
        (bounded_object_q_symmetric_product_pairs_cv
          semantic_left_gradient_bounds semantic_right_gradient_bounds)` by
       metis_tac [bounded_packed_q_symmetric_product_pairs_cv_valid]
  >> `LENGTH
        (bounded_object_q_symmetric_product_pairs_cv
          semantic_left_gradient_bounds semantic_right_gradient_bounds) = 21` by
       metis_tac
         [bounded_object_q_symmetric_product_pairs_cv_length6_relation]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_fused_hessian_cv
          runtime_left_value runtime_right_value
          runtime_left_hessian runtime_right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            runtime_left_gradient_bounds runtime_right_gradient_bounds))
        (bounded_object_q_interval_fused_hessian_cv
          semantic_left_value semantic_right_value
          semantic_left_hessian semantic_right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            semantic_left_gradient_bounds semantic_right_gradient_bounds))` by
       metis_tac [bounded_object_q_interval_fused_hessian_cv_rel]
  >> `EVERY bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_fused_hessian_cv
          semantic_left_value semantic_right_value
          semantic_left_hessian semantic_right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            semantic_left_gradient_bounds semantic_right_gradient_bounds))` by
       metis_tac [bounded_packed_q_interval_fused_hessian_cv_valid]
  >> `LENGTH
        (bounded_object_q_interval_fused_hessian_cv
          semantic_left_value semantic_right_value
          semantic_left_hessian semantic_right_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            semantic_left_gradient_bounds semantic_right_gradient_bounds)) = 21` by
       metis_tac
         [bounded_object_q_interval_fused_hessian_cv_length21_relation]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_mul_def,
        LET_THM]
  >> simp [LET_THM]
  >> irule
       compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv
  >> simp []
QED

val _ = export_theory ();
