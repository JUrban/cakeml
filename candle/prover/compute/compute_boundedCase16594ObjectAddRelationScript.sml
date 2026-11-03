(*****************************************************************************
 * Representation-independent addition relations for production object
 * states.  Runtime and semantic rational encodings may differ while denoting
 * the same interval values.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAddRelation
Ancestors
  compute_boundedCase16594ObjectAddControlEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_interval_list_add_cv_rel:
  !runtime_left semantic_left runtime_right semantic_right.
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_left semantic_left /\
    LIST_REL bounded_object_q_interval_cv_equiv
      runtime_right semantic_right /\
    LENGTH runtime_left = LENGTH runtime_right ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (MAP2 bounded_object_q_interval_add_cv runtime_left runtime_right)
      (MAP2 bounded_object_q_interval_add_cv semantic_left semantic_right)
Proof
  Induct
  >> Cases_on `semantic_left`
  >> Cases_on `runtime_right`
  >> Cases_on `semantic_right`
  >> simp [LIST_REL_def]
  >> metis_tac
       [compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong]
QED

Theorem bounded_case16594_object_interval_list_add_cv_valid:
  !left right.
    EVERY bounded_packed_q_interval_valid_cv left /\
    EVERY bounded_packed_q_interval_valid_cv right /\
    LENGTH left = LENGTH right ==>
    EVERY bounded_packed_q_interval_valid_cv
      (MAP2 bounded_object_q_interval_add_cv left right)
Proof
  Induct
  >> Cases_on `right`
  >> simp []
  >> metis_tac
       [compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add]
QED

Theorem bounded_case16594_object_interval_list_add_cv_length:
  LENGTH left = LENGTH right ==>
  LENGTH (MAP2 bounded_object_q_interval_add_cv left right) = LENGTH left
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> simp []
QED

Theorem bounded_case16594_object_add_recomplete_runtime_semantic_equiv:
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
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_right_hessian semantic_right_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_right_hessian /\
  LENGTH semantic_right_hessian = 21 ==>
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_state_cv
      (if left_domain /\ right_domain then compute_exec$Num 1
       else compute_exec$Num 0)
      (bounded_object_q_interval_add_cv
        runtime_left_center runtime_right_center)
      (bounded_object_q_cv_list
        (MAP2 bounded_object_q_interval_add_cv
          runtime_left_center_gradient runtime_right_center_gradient))
      (bounded_packed_q_source_value_bound6_cv runtime_radii
        (bounded_object_q_interval_add_cv
          runtime_left_center runtime_right_center)
        (MAP2 bounded_object_q_interval_add_cv
          runtime_left_center_gradient runtime_right_center_gradient)
        (MAP2 bounded_object_q_interval_add_cv
          runtime_left_hessian runtime_right_hessian))
      (bounded_object_q_cv_list
        (bounded_packed_q_source_gradient_complete6_cv runtime_radii
          (MAP2 bounded_object_q_interval_add_cv
            runtime_left_center_gradient runtime_right_center_gradient)
          (MAP2 bounded_object_q_interval_add_cv
            runtime_left_hessian runtime_right_hessian)))
      (bounded_object_q_cv_list
        (MAP2 bounded_object_q_interval_add_cv
          runtime_left_hessian runtime_right_hessian)))
    (bounded_object_q_taylor_add semantic_radii weights
      (BoundedObjectQTaylor left_domain semantic_left_center
        semantic_left_center_gradient semantic_left_value
        semantic_left_gradient_bounds semantic_left_hessian)
      (BoundedObjectQTaylor right_domain semantic_right_center
        semantic_right_center_gradient semantic_right_value
        semantic_right_gradient_bounds semantic_right_hessian))
Proof
  rpt gen_tac
  >> strip_tac
  >> simp
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_add_def,
        LET_THM]
  >> irule
       compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv
  >> simp []
  >> rpt conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_packed_q_interval_valid_cv_add
      >> simp [])
  >- (irule bounded_case16594_object_interval_list_add_cv_valid
      >> simp [])
  >- (irule bounded_case16594_object_interval_list_add_cv_valid
      >> simp [])
  >- (irule
        compute_boundedCase16594ObjectMulRelationTheory.bounded_object_q_interval_add_cv_equiv_cong
      >> simp [])
  >- (irule bounded_case16594_object_interval_list_add_cv_rel
      >> simp []
      >> metis_tac [LIST_REL_LENGTH])
  >> irule bounded_case16594_object_interval_list_add_cv_rel
  >> simp []
  >> metis_tac [LIST_REL_LENGTH]
QED

val _ = export_theory ();
