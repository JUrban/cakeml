(*****************************************************************************
 * Representation invariance of the object-q interval enclosure relation.
 *
 * Recompletion frequently changes rational encodings without changing their
 * values.  Certificate enclosure must therefore be transportable across the
 * established endpoint equivalence relation.
 *****************************************************************************)
Theory compute_boundedObjectIntervalEnclosesEquivalence
Ancestors
  compute_boundedAnalyticObjectAtanOperationRefinement
  compute_boundedCase16594ObjectRuntimePreservation
  compute_boundedPackedObjectAcceptRefinement
Libs
  bossLib preamble intLib

Theorem bounded_object_q_interval_encloses_pair_iff:
  bounded_object_q_encoded outer_lower /\
  bounded_object_q_encoded outer_upper /\
  bounded_object_q_encoded inner_lower /\
  bounded_object_q_encoded inner_upper ==>
  (bounded_object_q_interval_encloses
      (Pair outer_lower outer_upper) (Pair inner_lower inner_upper) <=>
   bounded_object_q_le_cv outer_lower outer_upper /\
   bounded_object_q_le_cv inner_lower inner_upper /\
   bounded_object_q_le_cv outer_lower inner_lower /\
   bounded_object_q_le_cv inner_upper outer_upper)
Proof
  rw [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def]
  >> PairCases_on `fraction`
  >> PairCases_on `fraction'`
  >> PairCases_on `fraction''`
  >> PairCases_on `fraction'''`
  >> simp
       [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_interval_encloses_def,
        compute_boundedObjectIntervalRelationTheory.bounded_object_q_interval_ints_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectProductRefinementTheory.bounded_object_q_le_cv_correct
  >> fs
       [compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >> imp_res_tac
       compute_boundedObjectIntervalRelationTheory.bounded_object_q_ints_denominator_positive
  >> simp []
QED

Theorem bounded_object_q_interval_encloses_equiv_inner:
  bounded_object_q_interval_encoded outer /\
  bounded_object_q_interval_encoded left /\
  bounded_object_q_interval_encoded right /\
  bounded_object_q_interval_cv_equiv left right /\
  bounded_object_q_interval_encloses outer right ==>
  bounded_object_q_interval_encloses outer left
Proof
  strip_tac
  >> mp_tac
       (Q.INST [`object_interval` |-> `outer`]
         compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `outer_lower`
       (qx_choose_then `outer_upper` strip_assume_tac))
  >> mp_tac
       (Q.INST [`object_interval` |-> `left`]
         compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `left_lower`
       (qx_choose_then `left_upper` strip_assume_tac))
  >> mp_tac
       (Q.INST [`object_interval` |-> `right`]
         compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `right_lower`
       (qx_choose_then `right_upper` strip_assume_tac))
  >> gvs
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def]
  >> `bounded_object_q_le_cv outer_lower right_lower /\
      bounded_object_q_le_cv right_upper outer_upper` by
       metis_tac [bounded_object_q_interval_encloses_pair_iff]
  >> `bounded_object_q_le_cv outer_lower left_lower =
        bounded_object_q_le_cv outer_lower right_lower` by
       (irule
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong
        >> simp []
        >> irule
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl
        >> fs [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def])
  >> `bounded_object_q_le_cv left_upper outer_upper =
        bounded_object_q_le_cv right_upper outer_upper` by
       (irule
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong
        >> simp []
        >> irule
             compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_refl
        >> fs [compute_boundedQFoldRelationTheory.bounded_object_q_encoded_def])
  >> `bounded_object_q_le_cv left_lower left_upper =
        bounded_object_q_le_cv right_lower right_upper` by
       (irule
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_le_cv_equiv_cong
        >> simp [])
  >> metis_tac [bounded_object_q_interval_encloses_pair_iff]
QED

val _ = export_theory ();
