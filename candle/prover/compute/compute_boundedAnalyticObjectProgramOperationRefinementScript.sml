(*****************************************************************************
 * Complete object-q state refinements for the arithmetic operations used by
 * the generic postfix program executor.
 *
 * The lower-level interval and fused-product refinements are already proved.
 * This theory packages their completed Taylor states behind one uniform
 * operation boundary so the subsequent stack/program induction does not
 * duplicate completion arithmetic.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectProgramOperationRefinement
Ancestors
  compute_boundedAnalyticObjectAtanOperationRefinement
  compute_boundedTaylorProgram
Libs
  bossLib preamble

Theorem bounded_taylor64_neg_complete_covers_object_q_state:
  bounded_taylor64_covers_object_q_state source object_domain
      object_center_value object_center_gradient object_value_bound
      object_gradient_bounds object_hessian /\
  bounded_taylor64_neg_complete radii source = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result object_domain
      (bounded_object_q_interval_neg_cv object_center_value)
      (MAP bounded_object_q_interval_neg_cv object_center_gradient)
      (bounded_object_q_taylor_value_complete_cv
        (bounded_object_q_interval_neg_cv object_center_value)
        (bounded_object_q_taylor_error_cv radii
          (MAP bounded_object_q_interval_neg_cv object_center_gradient)
          weights
          (MAP bounded_object_q_interval_neg_cv object_hessian)))
      (bounded_object_q_taylor_gradient_complete_cv radii
        (MAP bounded_object_q_interval_neg_cv object_center_gradient)
        (MAP bounded_object_q_interval_neg_cv object_hessian))
      (MAP bounded_object_q_interval_neg_cv object_hessian)
Proof
  Cases_on `source`
  >> rename1
       `BoundedTaylor64 source_domain source_center source_center_gradient
          source_value source_gradient_bounds source_hessian`
  >> rw [compute_boundedTaylorProgramTheory.bounded_taylor64_neg_complete_def]
  >> every_case_tac
  >> gvs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`, `result_domain` |-> `object_domain`,
          `center_value` |-> `bounded_interval64_neg source_center`,
          `object_center_value` |->
            `bounded_object_q_interval_neg_cv object_center_value`,
          `center_gradient` |->
            `bounded_interval64_list_neg source_center_gradient`,
          `object_center_gradient` |->
            `MAP bounded_object_q_interval_neg_cv object_center_gradient`,
          `hessian` |-> `bounded_interval64_list_neg source_hessian`,
          `object_hessian` |->
            `MAP bounded_object_q_interval_neg_cv object_hessian`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectTaylorRefinementTheory.bounded_taylor64_complete_covers_object_q_state)
  >> impl_tac
  >- metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_list_neg_covers_object_q]
  >> simp []
QED

Theorem bounded_taylor64_add_complete_covers_object_q_state:
  bounded_taylor64_covers_object_q_state left left_object_domain
      left_object_center_value left_object_center_gradient
      left_object_value_bound left_object_gradient_bounds
      left_object_hessian /\
  bounded_taylor64_covers_object_q_state right right_object_domain
      right_object_center_value right_object_center_gradient
      right_object_value_bound right_object_gradient_bounds
      right_object_hessian /\
  bounded_taylor64_add_complete radii left right = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result
      (left_object_domain /\ right_object_domain)
      (bounded_object_q_interval_add_cv
        left_object_center_value right_object_center_value)
      (MAP2 bounded_object_q_interval_add_cv
        left_object_center_gradient right_object_center_gradient)
      (bounded_object_q_taylor_value_complete_cv
        (bounded_object_q_interval_add_cv
          left_object_center_value right_object_center_value)
        (bounded_object_q_taylor_error_cv radii
          (MAP2 bounded_object_q_interval_add_cv
            left_object_center_gradient right_object_center_gradient)
          weights
          (MAP2 bounded_object_q_interval_add_cv
            left_object_hessian right_object_hessian)))
      (bounded_object_q_taylor_gradient_complete_cv radii
        (MAP2 bounded_object_q_interval_add_cv
          left_object_center_gradient right_object_center_gradient)
        (MAP2 bounded_object_q_interval_add_cv
          left_object_hessian right_object_hessian))
      (MAP2 bounded_object_q_interval_add_cv
        left_object_hessian right_object_hessian)
Proof
  Cases_on `left`
  >> rename1
       `BoundedTaylor64 left_domain left_center left_center_gradient
          left_value left_gradient_bounds left_hessian`
  >> Cases_on `right`
  >> rename1
       `BoundedTaylor64 right_domain right_center right_center_gradient
          right_value right_gradient_bounds right_hessian`
  >> rw [compute_boundedTaylorProgramTheory.bounded_taylor64_add_complete_def]
  >> every_case_tac
  >> gvs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> rename1
       `bounded_taylor64_complete radii
          (left_object_domain /\ right_object_domain)
          word_center word_center_gradient word_hessian = SOME result`
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`,
          `result_domain` |->
            `left_object_domain /\ right_object_domain`,
          `center_value` |-> `word_center`,
          `object_center_value` |->
            `bounded_object_q_interval_add_cv
              left_object_center_value right_object_center_value`,
          `center_gradient` |-> `word_center_gradient`,
          `object_center_gradient` |->
            `MAP2 bounded_object_q_interval_add_cv
              left_object_center_gradient right_object_center_gradient`,
          `hessian` |-> `word_hessian`,
          `object_hessian` |->
            `MAP2 bounded_object_q_interval_add_cv
              left_object_hessian right_object_hessian`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectTaylorRefinementTheory.bounded_taylor64_complete_covers_object_q_state)
  >> impl_tac
  >- metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_list_add_covers_object_q]
  >> simp []
QED

Theorem bounded_taylor64_mul_covers_object_q_state:
  bounded_taylor64_covers_object_q_state left left_object_domain
      left_object_center_value left_object_center_gradient
      left_object_value_bound left_object_gradient_bounds
      left_object_hessian /\
  bounded_taylor64_covers_object_q_state right right_object_domain
      right_object_center_value right_object_center_gradient
      right_object_value_bound right_object_gradient_bounds
      right_object_hessian /\
  bounded_taylor64_mul radii left right = SOME result ==>
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result
      (left_object_domain /\ right_object_domain)
      (bounded_object_q_interval_mul_cv
        left_object_center_value right_object_center_value)
      (bounded_object_q_interval_fused_scale_add_cv
        right_object_center_value left_object_center_gradient
        left_object_center_value right_object_center_gradient)
      (bounded_object_q_taylor_value_complete_cv
        (bounded_object_q_interval_mul_cv
          left_object_center_value right_object_center_value)
        (bounded_object_q_taylor_error_cv radii
          (bounded_object_q_interval_fused_scale_add_cv
            right_object_center_value left_object_center_gradient
            left_object_center_value right_object_center_gradient)
          weights
          (bounded_object_q_interval_fused_hessian_cv
            left_object_value_bound right_object_value_bound
            left_object_hessian right_object_hessian
            (bounded_object_q_symmetric_product_pairs_cv
              left_object_gradient_bounds right_object_gradient_bounds))))
      (bounded_object_q_taylor_gradient_complete_cv radii
        (bounded_object_q_interval_fused_scale_add_cv
          right_object_center_value left_object_center_gradient
          left_object_center_value right_object_center_gradient)
        (bounded_object_q_interval_fused_hessian_cv
          left_object_value_bound right_object_value_bound
          left_object_hessian right_object_hessian
          (bounded_object_q_symmetric_product_pairs_cv
            left_object_gradient_bounds right_object_gradient_bounds)))
      (bounded_object_q_interval_fused_hessian_cv
        left_object_value_bound right_object_value_bound
        left_object_hessian right_object_hessian
        (bounded_object_q_symmetric_product_pairs_cv
          left_object_gradient_bounds right_object_gradient_bounds))
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`left` |-> `left`, `right` |-> `right`,
          `left_object_domain` |-> `left_object_domain`,
          `left_object_center_value` |-> `left_object_center_value`,
          `left_object_center_gradient` |-> `left_object_center_gradient`,
          `left_object_value_bound` |-> `left_object_value_bound`,
          `left_object_gradient_bounds` |-> `left_object_gradient_bounds`,
          `left_object_hessian` |-> `left_object_hessian`,
          `right_object_domain` |-> `right_object_domain`,
          `right_object_center_value` |-> `right_object_center_value`,
          `right_object_center_gradient` |-> `right_object_center_gradient`,
          `right_object_value_bound` |-> `right_object_value_bound`,
          `right_object_gradient_bounds` |-> `right_object_gradient_bounds`,
          `right_object_hessian` |-> `right_object_hessian`,
          `radii` |-> `radii`, `result` |-> `result`]
         compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_taylor64_mul_reaches_object_q_complete_inputs)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `center_value`
         (qx_choose_then `center_gradient`
           (qx_choose_then `hessian` strip_assume_tac)))
  >> mp_tac
       (Q.INST
         [`radii` |-> `radii`,
          `result_domain` |->
            `left_object_domain /\ right_object_domain`,
          `center_value` |-> `center_value`,
          `object_center_value` |->
            `bounded_object_q_interval_mul_cv
              left_object_center_value right_object_center_value`,
          `center_gradient` |-> `center_gradient`,
          `object_center_gradient` |->
            `bounded_object_q_interval_fused_scale_add_cv
              right_object_center_value left_object_center_gradient
              left_object_center_value right_object_center_gradient`,
          `hessian` |-> `hessian`,
          `object_hessian` |->
            `bounded_object_q_interval_fused_hessian_cv
              left_object_value_bound right_object_value_bound
              left_object_hessian right_object_hessian
              (bounded_object_q_symmetric_product_pairs_cv
                left_object_gradient_bounds right_object_gradient_bounds)`,
          `result` |-> `result`]
         compute_boundedAnalyticObjectTaylorRefinementTheory.bounded_taylor64_complete_covers_object_q_state)
  >> impl_tac
  >- fs
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_taylor64_complete_inputs_cover_object_q_def]
  >> simp []
QED

val _ = export_theory ();
