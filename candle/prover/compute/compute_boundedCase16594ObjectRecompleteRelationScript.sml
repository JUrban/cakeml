(*****************************************************************************
 * Representation-independent semantic relation for production recompletion.
 *
 * The production checker uses exact rational radii and right-associated
 * source folds.  The object-q Taylor semantics uses word radii and
 * accumulator folds.  This theory joins both implementations through their
 * already-proved ordinary exact-rational contract before any instruction
 * evaluator or genuine certificate trace is involved.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectRecompleteRelation
Ancestors
  compute_boundedCase16594ObjectStateRecompleteEval
  compute_boundedPackedObjectSourceContractRefinement
Libs
  bossLib preamble intLib

Theorem bounded_packed_q_interval_valid_cv_object_encoded:
  bounded_packed_q_interval_valid_cv value ==>
  bounded_object_q_interval_encoded value
Proof
  metis_tac
    [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def,
     compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
QED

Theorem bounded_packed_q_source_error6_word_semantic_equiv:
  bounded_taylor_radius_pairs radii = SOME weights /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_error6_cv
      (MAP bounded_word64_object_q_cv radii) center_gradient hessian)
    (bounded_object_q_taylor_error_cv
      radii center_gradient weights hessian)
Proof
  strip_tac
  >> `bounded_object_q_exact_radius_pairs6_cv
        (MAP bounded_word64_object_q_cv radii) =
      SOME
        (MAP
          (\(left_radius,right_radius,double).
            (bounded_word64_object_q_cv left_radius,
             bounded_word64_object_q_cv right_radius,double))
          weights)` by
       metis_tac
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_radius_pairs_word_radii]
  >> `EVERY bounded_object_q_encoded
        (MAP bounded_word64_object_q_cv radii)` by
       simp
         [listTheory.EVERY_MAP,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_error6_cv
          (MAP bounded_word64_object_q_cv radii)
          center_gradient hessian)
        (bounded_object_q_exact_packed_error6_cv
          (MAP bounded_word64_object_q_cv radii)
          center_gradient hessian)` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_source_error6_equiv]
  >> `bounded_object_q_exact_packed_error6_cv
        (MAP bounded_word64_object_q_cv radii)
        center_gradient hessian =
      bounded_object_q_ordinary_error_cv
        radii center_gradient weights hessian` by
       metis_tac
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_packed_error_word_radii]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> `EVERY bounded_object_q_interval_encoded center_gradient` by
       fs
         [listTheory.EVERY_MEM,
          bounded_packed_q_interval_valid_cv_object_encoded]
  >> `EVERY bounded_object_q_interval_encoded hessian` by
       fs
         [listTheory.EVERY_MEM,
          bounded_packed_q_interval_valid_cv_object_encoded]
  >> `EVERY bounded_object_q_encoded
        (bounded_object_q_dot_terms_cv radii center_gradient)` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_dot_terms_encoded]
  >> `EVERY bounded_object_q_encoded
        (bounded_object_q_quadratic_terms_cv weights hessian)` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_quadratic_terms_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian)
        (bounded_object_q_ordinary_error_cv
          radii center_gradient weights hessian)` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_object_error_ordinary_equiv]
  >> metis_tac
       [compute_boundedQRelationAlgebraTheory.bounded_case10173_q_cv_equiv_sym,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans]
QED

Theorem bounded_packed_q_source_half_error_word_semantic_equiv:
  bounded_taylor_radius_pairs radii = SOME weights /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_half_error_cv
      (MAP bounded_word64_object_q_cv radii) center_gradient hessian)
    (bounded_object_q_half_cv
      (bounded_object_q_taylor_error_cv
        radii center_gradient weights hessian))
Proof
  strip_tac
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_error6_cv
          (MAP bounded_word64_object_q_cv radii)
          center_gradient hessian)
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian)` by
       metis_tac [bounded_packed_q_source_error6_word_semantic_equiv]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> `EVERY bounded_object_q_interval_encoded center_gradient` by
       fs
         [listTheory.EVERY_MEM,
          bounded_packed_q_interval_valid_cv_object_encoded]
  >> `EVERY bounded_object_q_interval_encoded hessian` by
       fs
         [listTheory.EVERY_MEM,
          bounded_packed_q_interval_valid_cv_object_encoded]
  >> `bounded_object_q_encoded
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian)` by
       (irule
          compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_taylor_error_cv_encoded
        >> simp [])
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv
          (bounded_analytic_source_q_cv 1 0 1)
          (bounded_packed_q_source_error6_cv
            (MAP bounded_word64_object_q_cv radii)
            center_gradient hessian))
        (bounded_object_q_mul_cv
          (bounded_analytic_source_q_cv 1 0 1)
          (bounded_object_q_taylor_error_cv
            radii center_gradient weights hessian))` by
       (irule
          compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
        >> simp
          [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded,
           compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl])
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv
          (bounded_analytic_source_q_cv 1 0 1)
          (bounded_object_q_taylor_error_cv
            radii center_gradient weights hessian))
        (bounded_object_q_mul_cv
          (bounded_object_q_taylor_error_cv
            radii center_gradient weights hessian)
          (bounded_analytic_source_q_cv 1 0 1))` by
       (irule
          compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_comm_equiv
        >> simp
          [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded])
  >> rw
       [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_half_error_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_half_cv_def]
  >> metis_tac
       [compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans]
QED

Theorem bounded_packed_q_source_value_bound6_word_semantic_equiv:
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_packed_q_interval_valid_cv center_value /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_object_q_interval_cv_equiv
    (bounded_packed_q_source_value_bound6_cv
      (MAP bounded_word64_object_q_cv radii)
      center_value center_gradient hessian)
    (bounded_object_q_taylor_value_complete_cv center_value
      (bounded_object_q_taylor_error_cv
        radii center_gradient weights hessian))
Proof
  strip_tac
  >> `bounded_object_q_interval_encoded center_value` by
       metis_tac [bounded_packed_q_interval_valid_cv_object_encoded]
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_half_error_cv
          (MAP bounded_word64_object_q_cv radii)
          center_gradient hessian)
        (bounded_object_q_half_cv
          (bounded_object_q_taylor_error_cv
            radii center_gradient weights hessian))` by
       metis_tac
         [bounded_packed_q_source_half_error_word_semantic_equiv]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_neg_cv
          (bounded_packed_q_source_half_error_cv
            (MAP bounded_word64_object_q_cv radii)
            center_gradient hessian))
        (bounded_object_q_neg_cv
          (bounded_object_q_half_cv
            (bounded_object_q_taylor_error_cv
              radii center_gradient weights hessian)))` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_neg_cv_equiv_cong]
  >> gvs []
  >> rw
       [compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_value_bound6_cv_def,
        compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def,
        LET_THM,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
QED

Theorem bounded_packed_q_source_dot_abs_upper_word_semantic_equiv:
  LENGTH radii = LENGTH entries /\
  EVERY bounded_packed_q_interval_valid_cv entries ==>
  bounded_case10173_q_cv_equiv
    (bounded_packed_q_source_dot_abs_upper_cv
      (MAP bounded_word64_object_q_cv radii) entries)
    (bounded_object_q_dot_abs_upper_acc_cv radii entries
      (bounded_word64_object_q_cv 0w))
Proof
  strip_tac
  >> `EVERY bounded_object_q_encoded
        (MAP bounded_word64_object_q_cv radii)` by
       simp
         [listTheory.EVERY_MAP,
          compute_boundedPackedObjectAcceptRefinementTheory.bounded_word64_object_q_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_dot_abs_upper_cv
          (MAP bounded_word64_object_q_cv radii) entries)
        (bounded_object_q_right_sum_cv
          (bounded_object_q_exact_dot_terms_cv
            (MAP bounded_word64_object_q_cv radii) entries))` by
       metis_tac
         [compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_source_dot_abs_upper_equiv]
  >> `bounded_object_q_exact_dot_terms_cv
        (MAP bounded_word64_object_q_cv radii) entries =
      bounded_object_q_dot_terms_cv radii entries` by
       simp
         [compute_boundedPackedObjectEntryContractTheory.bounded_object_q_exact_dot_terms_word_radii]
  >> `EVERY bounded_object_q_interval_encoded entries` by
       fs
         [listTheory.EVERY_MEM,
          bounded_packed_q_interval_valid_cv_object_encoded]
  >> `EVERY bounded_object_q_encoded
        (bounded_object_q_dot_terms_cv radii entries)` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_dot_terms_encoded]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_dot_abs_upper_acc_cv radii entries
          (bounded_word64_object_q_cv 0w))
        (bounded_object_q_right_sum_cv
          (bounded_object_q_dot_terms_cv radii entries))` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_dot_left_right_equiv]
  >> metis_tac
       [compute_boundedQRelationAlgebraTheory.bounded_case10173_q_cv_equiv_sym,
        compute_boundedQNormalizeRelationTheory.bounded_case10173_q_cv_equiv_trans]
QED

Theorem bounded_packed_q_source_gradient_row_word_semantic_equiv:
  LENGTH radii = 6 /\
  bounded_packed_q_interval_valid_cv center_entry /\
  EVERY bounded_packed_q_interval_valid_cv hessian_row /\
  LENGTH hessian_row = 6 ==>
  bounded_object_q_interval_cv_equiv
    (bounded_packed_q_source_gradient_row_complete_cv
      (MAP bounded_word64_object_q_cv radii)
      center_entry hessian_row)
    (bounded_object_q_taylor_gradient_row_complete_cv center_entry
      (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
        (bounded_word64_object_q_cv 0w)))
Proof
  strip_tac
  >> `bounded_object_q_interval_encoded center_entry` by
       metis_tac [bounded_packed_q_interval_valid_cv_object_encoded]
  >> imp_res_tac
       compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_shape
  >> `bounded_case10173_q_cv_equiv
        (bounded_packed_q_source_dot_abs_upper_cv
          (MAP bounded_word64_object_q_cv radii) hessian_row)
        (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
          (bounded_word64_object_q_cv 0w))` by
       metis_tac
         [bounded_packed_q_source_dot_abs_upper_word_semantic_equiv]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_add_cv
          (bounded_packed_q_source_dot_abs_upper_cv
            (MAP bounded_word64_object_q_cv radii) hessian_row)
          (bounded_packed_q_source_dot_abs_upper_cv
            (MAP bounded_word64_object_q_cv radii) hessian_row))
        (bounded_object_q_add_cv
          (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
            (bounded_word64_object_q_cv 0w))
          (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
            (bounded_word64_object_q_cv 0w)))` by
       metis_tac
         [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong]
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_mul_cv
          (bounded_object_q_add_cv
            (bounded_packed_q_source_dot_abs_upper_cv
              (MAP bounded_word64_object_q_cv radii) hessian_row)
            (bounded_packed_q_source_dot_abs_upper_cv
              (MAP bounded_word64_object_q_cv radii) hessian_row))
          (bounded_analytic_source_q_cv 1 0 1))
        (bounded_object_q_mul_cv
          (bounded_object_q_add_cv
            (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
              (bounded_word64_object_q_cv 0w))
            (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
              (bounded_word64_object_q_cv 0w)))
          (bounded_analytic_source_q_cv 1 0 1))` by
       (irule
          compute_boundedQFoldRelationTheory.bounded_object_q_mul_cv_equiv_cong
        >> simp
          [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_half_constant_encoded,
           compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl])
  >> `bounded_case10173_q_cv_equiv
        (bounded_object_q_neg_cv
          (bounded_object_q_mul_cv
            (bounded_object_q_add_cv
              (bounded_packed_q_source_dot_abs_upper_cv
                (MAP bounded_word64_object_q_cv radii) hessian_row)
              (bounded_packed_q_source_dot_abs_upper_cv
                (MAP bounded_word64_object_q_cv radii) hessian_row))
            (bounded_analytic_source_q_cv 1 0 1)))
        (bounded_object_q_neg_cv
          (bounded_object_q_mul_cv
            (bounded_object_q_add_cv
              (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
                (bounded_word64_object_q_cv 0w))
              (bounded_object_q_dot_abs_upper_acc_cv radii hessian_row
                (bounded_word64_object_q_cv 0w)))
            (bounded_analytic_source_q_cv 1 0 1)))` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_neg_cv_equiv_cong]
  >> gvs []
  >> rw
       [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_row_complete_cv_def,
        compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_row_complete_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_taylor_value_complete_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_symmetric_half_interval_cv_def,
        compute_boundedAnalyticObjectCompleteRefinementTheory.bounded_object_q_half_cv_def,
        compute_boundedPackedObjectValueEvalTheory.bounded_packed_q_source_interval_add_cv_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_add_cv_def,
        LET_THM,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_def]
  >> metis_tac
       [compute_boundedQFoldRelationTheory.bounded_object_q_add_cv_equiv_cong,
        compute_boundedQFoldRelationTheory.bounded_object_q_encoded_equiv_refl]
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

Theorem bounded_packed_q_source_gradient_rows_word_semantic_rel:
  !center_gradient rows.
    LENGTH radii = 6 /\
    LENGTH center_gradient = LENGTH rows /\
    EVERY bounded_packed_q_interval_valid_cv center_gradient /\
    EVERY
      (\row.
        LENGTH row = 6 /\
        EVERY bounded_packed_q_interval_valid_cv row) rows ==>
    LIST_REL bounded_object_q_interval_cv_equiv
      (bounded_packed_q_source_gradient_rows_complete_cv
        (MAP bounded_word64_object_q_cv radii) center_gradient rows)
      (bounded_object_q_taylor_gradient_rows_complete_cv
        radii center_gradient rows)
Proof
  Induct_on `center_gradient`
  >> Cases_on `rows`
  >> simp
       [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_rows_complete_cv_def,
        compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_rows_complete_cv_def,
        LIST_REL_def]
  >> metis_tac [bounded_packed_q_source_gradient_row_word_semantic_equiv]
QED

Theorem bounded_packed_q_source_gradient_complete6_word_semantic_rel:
  LENGTH radii = 6 /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  LIST_REL bounded_object_q_interval_cv_equiv
    (bounded_packed_q_source_gradient_complete6_cv
      (MAP bounded_word64_object_q_cv radii)
      center_gradient hessian)
    (bounded_object_q_taylor_gradient_complete_cv
      radii center_gradient hessian)
Proof
  strip_tac
  >> drule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_hessian64_rows_length21
  >> strip_tac
  >> `LENGTH rows = 6 /\
      EVERY
        (\row.
          LENGTH row = 6 /\
          EVERY bounded_packed_q_interval_valid_cv row) rows` by
       metis_tac [bounded_hessian64_rows_valid]
  >> rw
       [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_complete6_cv_def,
        compute_boundedAnalyticObjectGradientRefinementTheory.bounded_object_q_taylor_gradient_complete_cv_def]
  >> irule bounded_packed_q_source_gradient_rows_word_semantic_rel
  >> simp []
QED

Theorem bounded_packed_q_interval_valid_list_rel_refl:
  EVERY bounded_packed_q_interval_valid_cv values ==>
  LIST_REL bounded_object_q_interval_cv_equiv values values
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_list_rel_refl
  >> fs
       [listTheory.EVERY_MEM,
        bounded_packed_q_interval_valid_cv_object_encoded]
QED

Theorem bounded_case16594_object_recomplete_word_semantic_equiv:
  !domain_flag.
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_packed_q_interval_valid_cv center_value /\
  EVERY bounded_packed_q_interval_valid_cv center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_valid_cv hessian /\
  LENGTH hessian = 21 ==>
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_state_cv
      (if domain_flag then Num 1 else Num 0)
      center_value
      (bounded_object_q_cv_list center_gradient)
      (bounded_packed_q_source_value_bound6_cv
        (MAP bounded_word64_object_q_cv radii)
        center_value center_gradient hessian)
      (bounded_object_q_cv_list
        (bounded_packed_q_source_gradient_complete6_cv
          (MAP bounded_word64_object_q_cv radii)
          center_gradient hessian))
      (bounded_object_q_cv_list hessian))
    (BoundedObjectQTaylor domain_flag center_value center_gradient
      (bounded_object_q_taylor_value_complete_cv center_value
        (bounded_object_q_taylor_error_cv
          radii center_gradient weights hessian))
      (bounded_object_q_taylor_gradient_complete_cv
        radii center_gradient hessian)
      hessian)
Proof
  gen_tac
  >> strip_tac
  >> `bounded_object_q_interval_cv_equiv center_value center_value` by
       metis_tac
         [bounded_packed_q_interval_valid_cv_object_encoded,
          compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_object_q_interval_cv_equiv_refl]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        center_gradient center_gradient` by
       metis_tac [bounded_packed_q_interval_valid_list_rel_refl]
  >> `bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_value_bound6_cv
          (MAP bounded_word64_object_q_cv radii)
          center_value center_gradient hessian)
        (bounded_object_q_taylor_value_complete_cv center_value
          (bounded_object_q_taylor_error_cv
            radii center_gradient weights hessian))` by
       metis_tac
         [bounded_packed_q_source_value_bound6_word_semantic_equiv]
  >> `LENGTH radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_gradient_complete6_cv
          (MAP bounded_word64_object_q_cv radii)
          center_gradient hessian)
        (bounded_object_q_taylor_gradient_complete_cv
          radii center_gradient hessian)` by
       metis_tac
         [bounded_packed_q_source_gradient_complete6_word_semantic_rel]
  >> `LIST_REL bounded_object_q_interval_cv_equiv hessian hessian` by
       metis_tac [bounded_packed_q_interval_valid_list_rel_refl]
  >> rw
       [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_fields]
QED

Theorem bounded_case16594_object_recomplete_runtime_semantic_equiv:
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
      runtime_center
      (bounded_object_q_cv_list runtime_center_gradient)
      (bounded_packed_q_source_value_bound6_cv runtime_radii
        runtime_center runtime_center_gradient runtime_hessian)
      (bounded_object_q_cv_list
        (bounded_packed_q_source_gradient_complete6_cv runtime_radii
          runtime_center_gradient runtime_hessian))
      (bounded_object_q_cv_list runtime_hessian))
    (BoundedObjectQTaylor domain_flag semantic_center
      semantic_center_gradient
      (bounded_object_q_taylor_value_complete_cv semantic_center
        (bounded_object_q_taylor_error_cv semantic_radii
          semantic_center_gradient weights semantic_hessian))
      (bounded_object_q_taylor_gradient_complete_cv semantic_radii
        semantic_center_gradient semantic_hessian)
      semantic_hessian)
Proof
  gen_tac
  >> strip_tac
  >> `LENGTH semantic_radii = 6 /\ LENGTH weights = 21` by
       metis_tac
         [compute_boundedPackedObjectAcceptRefinementTheory.bounded_taylor_radius_pairs_lengths]
  >> `LENGTH runtime_radii = 6` by
       metis_tac [LIST_REL_LENGTH,rich_listTheory.LENGTH_MAP]
  >> `LENGTH runtime_hessian = 21` by
       metis_tac [LIST_REL_LENGTH]
  >> `bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_value_bound6_cv runtime_radii
          runtime_center runtime_center_gradient runtime_hessian)
        (bounded_packed_q_source_value_bound6_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          semantic_center semantic_center_gradient semantic_hessian)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_value_bound6_cv_rel]
  >> `bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_value_bound6_cv runtime_radii
          runtime_center runtime_center_gradient runtime_hessian)
        (bounded_object_q_taylor_value_complete_cv semantic_center
          (bounded_object_q_taylor_error_cv semantic_radii
            semantic_center_gradient weights semantic_hessian))` by
       metis_tac
         [bounded_packed_q_source_value_bound6_word_semantic_equiv,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_cv_equiv_trans]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_gradient_complete6_cv runtime_radii
          runtime_center_gradient runtime_hessian)
        (bounded_packed_q_source_gradient_complete6_cv
          (MAP bounded_word64_object_q_cv semantic_radii)
          semantic_center_gradient semantic_hessian)` by
       metis_tac
         [compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_packed_q_source_gradient_complete6_cv_rel]
  >> `LIST_REL bounded_object_q_interval_cv_equiv
        (bounded_packed_q_source_gradient_complete6_cv runtime_radii
          runtime_center_gradient runtime_hessian)
        (bounded_object_q_taylor_gradient_complete_cv semantic_radii
          semantic_center_gradient semantic_hessian)` by
       metis_tac
         [bounded_packed_q_source_gradient_complete6_word_semantic_rel,
          compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_interval_list_rel_trans]
  >> rw
       [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_cv_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_runtime_equiv_fields]
QED

val _ = export_theory ();
