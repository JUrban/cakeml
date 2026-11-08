(*****************************************************************************
 * Representation-independent semantic preservation for object negation.
 *
 * Negation changes the center, gradient, and Hessian representations before
 * invoking production recompletion.  This theory proves that those changes
 * preserve both packed validity and the runtime/semantic relation, then uses
 * the general recompletion theorem without evaluating a genuine certificate.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectNegRelation
Ancestors
  compute_boundedCase16594ObjectRecompleteRelation
Libs
  bossLib preamble intLib

Theorem bounded_packed_q_interval_valid_cv_neg:
  bounded_packed_q_interval_valid_cv value ==>
  bounded_packed_q_interval_valid_cv
    (bounded_object_q_interval_neg_cv value)
Proof
  rw
    [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> qexists_tac
       `bounded_object_q_interval_neg_ints decoded`
  >> conj_tac
  >- metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_decodes]
  >> PairCases_on `decoded`
  >> fs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_interval_neg_ints_def,
        compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_q_interval_valid_cv_map_neg:
  !values.
    EVERY bounded_packed_q_interval_valid_cv values ==>
    EVERY bounded_packed_q_interval_valid_cv
      (MAP bounded_object_q_interval_neg_cv values)
Proof
  Induct
  >> simp [bounded_packed_q_interval_valid_cv_neg]
QED

Theorem bounded_case16594_object_neg_recomplete_runtime_semantic_equiv:
  !domain_flag.
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_object_q_interval_cv_equiv runtime_center semantic_center /\
  bounded_packed_q_interval_valid_cv semantic_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_gradient semantic_center_gradient /\
  EVERY bounded_packed_q_interval_valid_cv semantic_center_gradient /\
  LENGTH semantic_center_gradient = 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_hessian semantic_hessian /\
  EVERY bounded_packed_q_interval_valid_cv semantic_hessian /\
  LENGTH semantic_hessian = 21 ==>
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_state_cv
      (if domain_flag then Num 1 else Num 0)
      (bounded_object_q_interval_neg_cv runtime_center)
      (bounded_object_q_cv_list
        (MAP bounded_object_q_interval_neg_cv runtime_center_gradient))
      (bounded_packed_q_source_value_bound6_cv runtime_radii
        (bounded_object_q_interval_neg_cv runtime_center)
        (MAP bounded_object_q_interval_neg_cv runtime_center_gradient)
        (MAP bounded_object_q_interval_neg_cv runtime_hessian))
      (bounded_object_q_cv_list
        (bounded_packed_q_source_gradient_complete6_cv runtime_radii
          (MAP bounded_object_q_interval_neg_cv runtime_center_gradient)
          (MAP bounded_object_q_interval_neg_cv runtime_hessian)))
      (bounded_object_q_cv_list
        (MAP bounded_object_q_interval_neg_cv runtime_hessian)))
    (bounded_object_q_taylor_neg semantic_radii weights
      (BoundedObjectQTaylor domain_flag semantic_center
        semantic_center_gradient semantic_value semantic_gradient_bounds
        semantic_hessian))
Proof
  gen_tac
  >> strip_tac
  >> `bounded_object_q_interval_cv_equiv
        (bounded_object_q_interval_neg_cv runtime_center)
        (bounded_object_q_interval_neg_cv semantic_center)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_neg_cv_equiv_cong]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (MAP bounded_object_q_interval_neg_cv runtime_center_gradient)
        (MAP bounded_object_q_interval_neg_cv semantic_center_gradient)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_neg_rel]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (MAP bounded_object_q_interval_neg_cv runtime_hessian)
        (MAP bounded_object_q_interval_neg_cv semantic_hessian)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_neg_rel]
  >> `bounded_packed_q_interval_valid_cv
        (bounded_object_q_interval_neg_cv semantic_center)` by
       metis_tac [bounded_packed_q_interval_valid_cv_neg]
  >> `EVERY bounded_packed_q_interval_valid_cv
        (MAP bounded_object_q_interval_neg_cv semantic_center_gradient)` by
       metis_tac [bounded_packed_q_interval_valid_cv_map_neg]
  >> `EVERY bounded_packed_q_interval_valid_cv
        (MAP bounded_object_q_interval_neg_cv semantic_hessian)` by
       metis_tac [bounded_packed_q_interval_valid_cv_map_neg]
  >> PURE_REWRITE_TAC
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_object_q_taylor_neg_def,
        LET_THM]
  >> mp_tac
       (Q.INST
         [`runtime_center` |->
            `bounded_object_q_interval_neg_cv runtime_center`,
          `semantic_center` |->
            `bounded_object_q_interval_neg_cv semantic_center`,
          `runtime_center_gradient` |->
            `MAP bounded_object_q_interval_neg_cv runtime_center_gradient`,
          `semantic_center_gradient` |->
            `MAP bounded_object_q_interval_neg_cv semantic_center_gradient`,
          `runtime_hessian` |->
            `MAP bounded_object_q_interval_neg_cv runtime_hessian`,
          `semantic_hessian` |->
            `MAP bounded_object_q_interval_neg_cv semantic_hessian`]
         (Q.SPEC `domain_flag`
           compute_boundedCase16594ObjectRecompleteRelationTheory.bounded_case16594_object_recomplete_runtime_semantic_equiv))
  >> simp []
QED

val _ = export_theory ();
