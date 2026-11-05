(*****************************************************************************
 * Representation-independent transfer of the packed acceptance predicate.
 *
 * The production object evaluator may normalize exact rationals differently
 * from the semantic object run.  Acceptance depends only on their represented
 * values, so it must cross the established runtime-refinement relation rather
 * than require byte-for-byte cv equality.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectRuntimeAcceptTransfer
Ancestors
  compute_boundedCase16594ObjectPolyStackInvariant
  compute_boundedCase16594ObjectRuntimePreservation
  compute_boundedPackedObjectSourceContractRefinement
Libs
  bossLib preamble intLib

Theorem bounded_object_q_interval_encoded_is_packed:
  bounded_object_q_interval_encoded (object_interval:cv) ==>
  bounded_packed_q_interval_encoded object_interval
Proof
  strip_tac
  >> drule
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> rw
       [compute_boundedPackedObjectPrimitiveEvalTheory.bounded_packed_q_interval_encoded_def]
  >> metis_tac []
QED

Theorem bounded_object_q_interval_list_encoded_is_packed:
  !intervals.
    EVERY bounded_object_q_interval_encoded intervals ==>
    EVERY bounded_packed_q_interval_encoded intervals
Proof
  Induct
  >> simp [bounded_object_q_interval_encoded_is_packed]
QED

Theorem bounded_packed_q_source_interval_upper_cv_equiv_cong:
  bounded_object_q_interval_cv_equiv left right ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_interval_upper_cv left)
    (bounded_packed_q_source_interval_upper_cv right)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def,
        compute_boundedPackedObjectFinishEvalTheory.bounded_packed_q_source_interval_upper_cv_def]
QED

Theorem bounded_packed_object_source_accept6_rel:
  bounded_packed_object_source_accept6
      semantic_radii semantic_center semantic_center_gradient
      semantic_hessian /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii semantic_radii /\
  bounded_object_q_interval_cv_equiv runtime_center semantic_center /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_gradient semantic_center_gradient /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_hessian semantic_hessian /\
  bounded_object_q_interval_encoded runtime_center /\
  EVERY bounded_object_q_interval_encoded runtime_center_gradient /\
  EVERY bounded_object_q_interval_encoded runtime_hessian ==>
  bounded_packed_object_source_accept6
    runtime_radii runtime_center runtime_center_gradient runtime_hessian
Proof
  strip_tac
  >> `LENGTH semantic_radii = 6` by
       fs
         [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> `LENGTH semantic_center_gradient = 6` by
       fs
         [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> `LENGTH semantic_hessian = 21` by
       fs
         [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> `LENGTH runtime_radii = 6` by metis_tac [LIST_REL_LENGTH]
  >> `LENGTH runtime_center_gradient = 6` by metis_tac [LIST_REL_LENGTH]
  >> `LENGTH runtime_hessian = 21` by metis_tac [LIST_REL_LENGTH]
  >> `EVERY bounded_object_q_encoded runtime_radii` by
       metis_tac
         [compute_boundedCase16594Cell0AuthenticatedObjectPrefix10TraceTheory.bounded_case16594_q_equiv_list_left_encoded]
  >> `bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_value_bound6_cv runtime_radii runtime_center
          runtime_center_gradient runtime_hessian)
        (bounded_packed_q_source_value_bound6_cv semantic_radii semantic_center
          semantic_center_gradient semantic_hessian)` by
       (irule
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_value_bound6_cv_rel
        >> asm_rewrite_tac [])
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv runtime_radii runtime_center
            runtime_center_gradient runtime_hessian))
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv semantic_radii semantic_center
            semantic_center_gradient semantic_hessian))` by
       metis_tac [bounded_packed_q_source_interval_upper_cv_equiv_cong]
  >> `bounded_object_q_strict_negative_cv
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv semantic_radii semantic_center
            semantic_center_gradient semantic_hessian))` by
       fs
         [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv semantic_radii semantic_center
            semantic_center_gradient semantic_hessian))
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv runtime_radii runtime_center
            runtime_center_gradient runtime_hessian))` by
       metis_tac
         [compute_boundedQRelationAlgebraTheory.bounded_case10173_q_cv_equiv_sym]
  >> `bounded_object_q_strict_negative_cv
        (bounded_packed_q_source_interval_upper_cv
          (bounded_packed_q_source_value_bound6_cv runtime_radii runtime_center
            runtime_center_gradient runtime_hessian))` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_strict_negative_equiv]
  >> rw
       [compute_boundedPackedObjectEntryRefinementTheory.bounded_packed_object_source_accept6_def]
  >> asm_rewrite_tac []
  >> metis_tac
       [bounded_object_q_interval_encoded_is_packed,
        bounded_object_q_interval_list_encoded_is_packed]
QED

Theorem bounded_object_q_taylor_runtime_refines_source_accept6:
  bounded_packed_object_source_accept6
      semantic_radii semantic_center semantic_center_gradient
      semantic_hessian /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii semantic_radii /\
  bounded_object_q_taylor_runtime_refines runtime_state
    (BoundedObjectQTaylor T semantic_center semantic_center_gradient
      semantic_value_bound semantic_gradient_bounds semantic_hessian) ==>
  ?runtime_center runtime_center_gradient runtime_value_bound
      runtime_gradient_bounds runtime_hessian.
    runtime_state =
      bounded_case16594_object_state_cv (Num 1) runtime_center
        (bounded_object_q_cv_list runtime_center_gradient)
        runtime_value_bound
        (bounded_object_q_cv_list runtime_gradient_bounds)
        (bounded_object_q_cv_list runtime_hessian) /\
    bounded_packed_object_source_accept6
      runtime_radii runtime_center runtime_center_gradient runtime_hessian
Proof
  strip_tac
  >> drule
       compute_boundedCase16594ObjectPolyStackInvariantTheory.bounded_object_q_taylor_runtime_refines_contract
  >> strip_tac
  >> qexists_tac `runtime_center`
  >> qexists_tac `runtime_center_gradient`
  >> qexists_tac `runtime_value_bound`
  >> qexists_tac `runtime_gradient_bounds`
  >> qexists_tac `runtime_hessian`
  >> asm_rewrite_tac []
  >> irule bounded_packed_object_source_accept6_rel
  >> asm_rewrite_tac []
  >> qexists_tac `semantic_center`
  >> qexists_tac `semantic_center_gradient`
  >> qexists_tac `semantic_hessian`
  >> qexists_tac `semantic_radii`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
