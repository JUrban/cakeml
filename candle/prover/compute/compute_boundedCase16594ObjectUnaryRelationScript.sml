(*****************************************************************************
 * Representation-independent preservation for the shared production unary
 * Taylor constructor.  These lemmas are common to sqrt, inverse, and atan.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectUnaryRelation
Ancestors
  compute_boundedCase16594ObjectUnaryCompleteEval
  compute_boundedCase16594ObjectRecompleteRelation
  compute_boundedCase16594ObjectPolyStackInvariant
Libs
  bossLib preamble intLib

Theorem bounded_object_q_interval_list_scale_cv_rel:
  !runtime_values semantic_values.
    bounded_object_q_interval_cv_equiv runtime_scalar semantic_scalar /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_values semantic_values ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_list_scale_cv
        runtime_scalar runtime_values)
      (bounded_object_q_interval_list_scale_cv
        semantic_scalar semantic_values)
Proof
  Induct
  >> Cases_on `semantic_values`
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def,
        LIST_REL_def]
  >> fs
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> metis_tac
       [compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_mul_cv_equiv_cong]
QED

Theorem bounded_object_q_interval_self_outer_cv_rel:
  !runtime_values semantic_values.
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_values semantic_values ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (bounded_object_q_interval_self_outer_cv runtime_values)
      (bounded_object_q_interval_self_outer_cv semantic_values)
Proof
  Induct
  >> Cases_on `semantic_values`
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def,
        LIST_REL_def]
  >> metis_tac
       [listTheory.LIST_REL_APPEND_suff,
        bounded_object_q_interval_list_scale_cv_rel,
        LIST_REL_def]
QED

Theorem bounded_object_q_taylor_unary_hessian_cv_rel:
  bounded_object_q_interval_cv_equiv
      runtime_box_derivative semantic_box_derivative /\
  bounded_object_q_interval_cv_equiv
      runtime_box_second semantic_box_second /\
  LIST_REL bounded_object_q_interval_cv_equiv
      runtime_gradient_bounds semantic_gradient_bounds /\
  LIST_REL bounded_object_q_interval_cv_equiv
      runtime_hessian semantic_hessian /\
  LENGTH semantic_gradient_bounds = 6 /\
  LENGTH semantic_hessian = 21 ==>
  LIST_REL bounded_object_q_interval_cv_equiv
    (bounded_object_q_taylor_unary_hessian_cv
      runtime_box_derivative runtime_box_second
      runtime_gradient_bounds runtime_hessian)
    (bounded_object_q_taylor_unary_hessian_cv
      semantic_box_derivative semantic_box_second
      semantic_gradient_bounds semantic_hessian)
Proof
  strip_tac
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_self_outer_cv runtime_gradient_bounds)
        (bounded_object_q_interval_self_outer_cv semantic_gradient_bounds)` by
       metis_tac [bounded_object_q_interval_self_outer_cv_rel]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_list_scale_cv runtime_box_second
          (bounded_object_q_interval_self_outer_cv runtime_gradient_bounds))
        (bounded_object_q_interval_list_scale_cv semantic_box_second
          (bounded_object_q_interval_self_outer_cv semantic_gradient_bounds))` by
       metis_tac [bounded_object_q_interval_list_scale_cv_rel]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_list_scale_cv runtime_box_derivative
          runtime_hessian)
        (bounded_object_q_interval_list_scale_cv semantic_box_derivative
          semantic_hessian)` by
       metis_tac [bounded_object_q_interval_list_scale_cv_rel]
  >> rw
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_taylor_unary_hessian_cv_def]
  >> irule
       compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_rel
  >> simp []
  >> metis_tac
       [LIST_REL_LENGTH,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_self_outer_length6]
QED

Theorem bounded_packed_q_interval_valid_cv_list_scale:
  !values.
    bounded_packed_q_interval_valid_cv scalar /\
    EVERY bounded_packed_q_interval_valid_cv values ==>
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_object_q_interval_list_scale_cv scalar values)
Proof
  Induct
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> fs
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_list_scale_cv_def]
  >> metis_tac
       [compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_mul]
QED

Theorem bounded_packed_q_interval_valid_cv_self_outer:
  !values.
    EVERY bounded_packed_q_interval_valid_cv values ==>
    EVERY bounded_packed_q_interval_valid_cv
      (bounded_object_q_interval_self_outer_cv values)
Proof
  Induct
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_interval_self_outer_cv_def,
        bounded_packed_q_interval_valid_cv_list_scale]
QED

Theorem bounded_packed_q_interval_valid_cv_unary_hessian:
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_second /\
  EVERY bounded_packed_q_interval_valid_cv gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  EVERY bounded_packed_q_interval_valid_cv
    (bounded_object_q_taylor_unary_hessian_cv
      box_derivative box_second gradient_bounds hessian)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_taylor_unary_hessian_cv_def]
  >> irule
       compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_valid
  >> simp
       [bounded_packed_q_interval_valid_cv_list_scale,
        bounded_packed_q_interval_valid_cv_self_outer,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_self_outer_length6]
QED

Theorem bounded_object_q_taylor_unary_hessian_cv_length21:
  LENGTH gradient_bounds = 6 /\
  LENGTH hessian = 21 ==>
  LENGTH
    (bounded_object_q_taylor_unary_hessian_cv
      box_derivative box_second gradient_bounds hessian) = 21
Proof
  strip_tac
  >> simp
       [compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_object_q_taylor_unary_hessian_cv_def,
        compute_boundedCase16594ObjectAddRelationTheory.bounded_case16594_object_interval_list_add_cv_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_self_outer_length6]
QED

Theorem bounded_object_q_taylor_unary_semantic_valid:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_object_q_taylor_semantic_valid source /\
  bounded_packed_q_interval_valid_cv center_result /\
  bounded_packed_q_interval_valid_cv center_derivative /\
  bounded_packed_q_interval_valid_cv box_derivative /\
  bounded_packed_q_interval_valid_cv box_second ==>
  bounded_object_q_taylor_semantic_valid
    (bounded_object_q_taylor_unary radii weights result_domain
      center_result center_derivative box_derivative box_second source)
Proof
  Cases_on `source`
  >> strip_tac
  >> fs
       [compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_semantic_valid_def]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
        LET_THM]
  >> BETA_TAC
  >> irule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_recomplete_semantic_valid
  >> simp
       [bounded_packed_q_interval_valid_cv_list_scale,
        bounded_packed_q_interval_valid_cv_unary_hessian,
        bounded_object_q_taylor_unary_hessian_cv_length21,
        compute_boundedCase16594ObjectUnaryCoreEvalTheory.bounded_case16594_object_interval_list_scale_length]
QED

val _ = export_theory ();
