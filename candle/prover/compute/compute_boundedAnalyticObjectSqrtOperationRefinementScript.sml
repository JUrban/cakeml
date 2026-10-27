(*****************************************************************************
 * Operation-level object-q refinement for the scale-2^40 square-root lift.
 *
 * This proof-only layer exposes the successful executable trace and proves
 * that each reciprocal certificate necessarily took its positive branch.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectSqrtOperationRefinement
Ancestors
  compute_boundedAnalyticObjectReciprocalRefinement
Libs
  bossLib preamble intLib

Theorem bounded_interval64_valid_contains_lower:
  bounded_interval64_valid interval ==>
  bounded_interval64_contains_int interval
    (bounded_signed64_to_int (bounded_interval64_lower interval))
Proof
  Cases_on `interval`
  >> simp
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_interval64_add_self_nonnegative:
  bounded_interval64_valid input /\
  0 <= bounded_signed64_to_int (bounded_interval64_lower input) /\
  bounded_interval64_add input input = SOME result ==>
  0 <= bounded_signed64_to_int (bounded_interval64_lower result) /\
  0 <= bounded_signed64_to_int (bounded_interval64_upper result)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_add_value
  >> Cases_on `input`
  >> Cases_on `result`
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_contains_scaled_nonnegative_upper:
  bounded_interval64_contains_scaled_int interval scale value /\
  0 < scale /\
  0 <= value ==>
  0 <= bounded_signed64_to_int (bounded_interval64_upper interval)
Proof
  Cases_on `interval`
  >> rename1 `BoundedInterval64 lower upper`
  >> strip_tac
  >> match_mp_tac
       (Q.INST
         [`multiplier` |-> `scale`,
          `left` |-> `0:int`,
          `right` |-> `bounded_signed64_to_int upper`]
         compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_int_le_cancel_positive_left)
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_mul_nonnegative_upper:
  bounded_interval64_valid left /\
  bounded_interval64_valid right /\
  0 <= bounded_signed64_to_int (bounded_interval64_lower left) /\
  0 <= bounded_signed64_to_int (bounded_interval64_lower right) /\
  bounded_interval64_mul left right = SOME result ==>
  0 <= bounded_signed64_to_int (bounded_interval64_upper result)
Proof
  strip_tac
  >> `bounded_interval64_contains_int left
        (bounded_signed64_to_int (bounded_interval64_lower left))` by
       (irule bounded_interval64_valid_contains_lower
        >> asm_rewrite_tac [])
  >> `bounded_interval64_contains_int right
        (bounded_signed64_to_int (bounded_interval64_lower right))` by
       (irule bounded_interval64_valid_contains_lower
        >> asm_rewrite_tac [])
  >> `0 <= bounded_signed64_to_int (bounded_interval64_lower left) *
        bounded_signed64_to_int (bounded_interval64_lower right)` by
       (irule integerTheory.INT_LE_MUL >> asm_rewrite_tac [])
  >> match_mp_tac
       (Q.INST
         [`interval` |-> `result`,
          `scale` |-> `(&1099511627776:int)`,
          `value` |->
            `bounded_signed64_to_int (bounded_interval64_lower left) *
               bounded_signed64_to_int (bounded_interval64_lower right)`]
         bounded_interval64_contains_scaled_nonnegative_upper)
  >> simp []
  >> irule
       compute_boundedIntervalTheory.bounded_interval64_mul_contains_scaled_product
  >> qexists_tac `left`
  >> qexists_tac `right`
  >> asm_rewrite_tac []
QED

Theorem bounded_interval64_inv_certificate_nonnegative_upper_positive:
  bounded_interval64_inv_certificate input output /\
  0 <= bounded_signed64_to_int (bounded_interval64_upper input) ==>
  bounded_signed64_strict_positive (bounded_interval64_lower input)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> Cases_on `bounded_signed64_strict_positive b`
  >- fs [compute_boundedIntervalTheory.bounded_interval64_lower_def]
  >> fs
       [compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def]
  >> fs
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> `F` by intLib.ARITH_TAC
  >> fs []
QED

Theorem bounded_interval64_sqrt_certificate_valid_components:
  bounded_interval64_sqrt_certificate input output ==>
  bounded_interval64_valid input /\ bounded_interval64_valid output
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> strip_tac
  >> imp_res_tac
       compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_nonnegative
  >> asm_rewrite_tac []
QED

Theorem bounded_taylor64_sqrt_refinement_trace:
  bounded_taylor64_sqrt radii center_sqrt box_sqrt center_derivative
      box_derivative box_second_reciprocal source = SOME result ==>
  ?source_domain center_value center_gradient value_bound gradient_bounds
      hessian center_twice box_twice input_twice box_second_denominator.
    source =
      BoundedTaylor64 source_domain center_value center_gradient value_bound
        gradient_bounds hessian /\
    bounded_interval64_sqrt_certificate center_value center_sqrt /\
    bounded_interval64_sqrt_certificate value_bound box_sqrt /\
    bounded_interval64_add center_sqrt center_sqrt = SOME center_twice /\
    bounded_interval64_add box_sqrt box_sqrt = SOME box_twice /\
    bounded_interval64_add value_bound value_bound = SOME input_twice /\
    bounded_interval64_mul box_twice input_twice =
      SOME box_second_denominator /\
    bounded_interval64_inv_certificate center_twice center_derivative /\
    bounded_interval64_inv_certificate box_twice box_derivative /\
    bounded_interval64_inv_certificate
      box_second_denominator box_second_reciprocal /\
    bounded_taylor64_unary_complete radii T center_sqrt center_derivative
      box_derivative (bounded_interval64_neg box_second_reciprocal) source =
      SOME result
Proof
  Cases_on `source`
  >> rw [compute_boundedTaylorSqrtTheory.bounded_taylor64_sqrt_def]
  >> every_case_tac
  >> gvs []
  >> rpt (first_assum (irule_at Any))
QED

Theorem bounded_taylor64_sqrt_reaches_object_q_unary_inputs:
  bounded_taylor64_covers_object_q_state source object_source_domain
      object_source_center object_source_center_gradient object_source_value
      object_source_gradient_bounds object_source_hessian /\
  bounded_taylor64_sqrt radii center_sqrt box_sqrt center_derivative
      box_derivative box_second_reciprocal source = SOME result ==>
  bounded_object_q_sqrt_certificate_exact object_source_center
      (bounded_interval64_object_q_cv center_sqrt) /\
  bounded_object_q_sqrt_certificate_exact object_source_value
      (bounded_interval64_object_q_cv box_sqrt) /\
  bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_add_cv
        (bounded_interval64_object_q_cv center_sqrt)
        (bounded_interval64_object_q_cv center_sqrt))
      (bounded_interval64_object_q_cv center_derivative) /\
  bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_add_cv
        (bounded_interval64_object_q_cv box_sqrt)
        (bounded_interval64_object_q_cv box_sqrt))
      (bounded_interval64_object_q_cv box_derivative) /\
  bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_mul_cv
        (bounded_object_q_interval_add_cv
          (bounded_interval64_object_q_cv box_sqrt)
          (bounded_interval64_object_q_cv box_sqrt))
        (bounded_object_q_interval_add_cv
          object_source_value object_source_value))
      (bounded_interval64_object_q_cv box_second_reciprocal) /\
  bounded_interval64_covers_object_q center_sqrt
      (bounded_interval64_object_q_cv center_sqrt) /\
  bounded_interval64_covers_object_q center_derivative
      (bounded_interval64_object_q_cv center_derivative) /\
  bounded_interval64_covers_object_q box_derivative
      (bounded_interval64_object_q_cv box_derivative) /\
  bounded_interval64_covers_object_q
      (bounded_interval64_neg box_second_reciprocal)
      (bounded_object_q_interval_neg_cv
        (bounded_interval64_object_q_cv box_second_reciprocal)) /\
  bounded_taylor64_unary_complete radii T center_sqrt center_derivative
      box_derivative (bounded_interval64_neg box_second_reciprocal) source =
    SOME result
Proof
  strip_tac
  >> drule bounded_taylor64_sqrt_refinement_trace
  >> disch_then
       (qx_choose_then `source_domain`
         (qx_choose_then `center_value`
           (qx_choose_then `center_gradient`
             (qx_choose_then `value_bound`
               (qx_choose_then `gradient_bounds`
                 (qx_choose_then `hessian`
                   (qx_choose_then `center_twice`
                     (qx_choose_then `box_twice`
                       (qx_choose_then `input_twice`
                         (qx_choose_then `box_second_denominator`
                           strip_assume_tac))))))))))
  >> fs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> `bounded_interval64_valid center_value /\
      bounded_interval64_valid center_sqrt` by
       metis_tac [bounded_interval64_sqrt_certificate_valid_components]
  >> `bounded_interval64_valid value_bound /\
      bounded_interval64_valid box_sqrt` by
       metis_tac [bounded_interval64_sqrt_certificate_valid_components]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_lower center_sqrt)` by
       metis_tac
         [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_interval64_sqrt_certificate_components]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_lower box_sqrt)` by
       metis_tac
         [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_interval64_sqrt_certificate_components]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_lower value_bound)` by
       metis_tac
         [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_interval64_sqrt_certificate_components]
  >> `bounded_interval64_valid center_twice /\
      bounded_interval64_valid center_derivative` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_valid box_twice /\
      bounded_interval64_valid box_derivative` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_valid box_second_denominator /\
      bounded_interval64_valid box_second_reciprocal` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_valid input_twice` by
       metis_tac
         [compute_boundedIntervalAddTheory.bounded_interval64_add_value]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_upper center_twice)` by
       metis_tac [bounded_interval64_add_self_nonnegative]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_upper box_twice)` by
       metis_tac [bounded_interval64_add_self_nonnegative]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_lower input_twice)` by
       metis_tac [bounded_interval64_add_self_nonnegative]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_lower box_twice)` by
       metis_tac [bounded_interval64_add_self_nonnegative]
  >> `0 <= bounded_signed64_to_int
        (bounded_interval64_upper box_second_denominator)` by
       metis_tac [bounded_interval64_mul_nonnegative_upper]
  >> `bounded_signed64_strict_positive
        (bounded_interval64_lower center_twice)` by
       metis_tac [bounded_interval64_inv_certificate_nonnegative_upper_positive]
  >> `bounded_signed64_strict_positive
        (bounded_interval64_lower box_twice)` by
       metis_tac [bounded_interval64_inv_certificate_nonnegative_upper_positive]
  >> `bounded_signed64_strict_positive
        (bounded_interval64_lower box_second_denominator)` by
       metis_tac [bounded_interval64_inv_certificate_nonnegative_upper_positive]
  >> `bounded_interval64_covers_object_q center_sqrt
        (bounded_interval64_object_q_cv center_sqrt)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q box_sqrt
        (bounded_interval64_object_q_cv box_sqrt)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q center_derivative
        (bounded_interval64_object_q_cv center_derivative)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q box_derivative
        (bounded_interval64_object_q_cv box_derivative)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q box_second_reciprocal
        (bounded_interval64_object_q_cv box_second_reciprocal)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q center_twice
        (bounded_object_q_interval_add_cv
          (bounded_interval64_object_q_cv center_sqrt)
          (bounded_interval64_object_q_cv center_sqrt))` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q]
  >> `bounded_interval64_covers_object_q box_twice
        (bounded_object_q_interval_add_cv
          (bounded_interval64_object_q_cv box_sqrt)
          (bounded_interval64_object_q_cv box_sqrt))` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q]
  >> `bounded_interval64_covers_object_q input_twice
        (bounded_object_q_interval_add_cv
          object_source_value object_source_value)` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q]
  >> `bounded_interval64_covers_object_q box_second_denominator
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv
            (bounded_interval64_object_q_cv box_sqrt)
            (bounded_interval64_object_q_cv box_sqrt))
          (bounded_object_q_interval_add_cv
            object_source_value object_source_value))` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q]
  >> rpt conj_tac
  >- metis_tac
       [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_interval64_sqrt_certificate_covers_object_q]
  >- metis_tac
       [compute_boundedAnalyticObjectSqrtRefinementTheory.bounded_interval64_sqrt_certificate_covers_object_q]
  >- metis_tac
       [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_positive_inv_certificate_covers_object_q]
  >- metis_tac
       [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_positive_inv_certificate_covers_object_q]
  >- metis_tac
       [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_positive_inv_certificate_covers_object_q]
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q]
  >> asm_rewrite_tac []
QED

Theorem bounded_taylor64_sqrt_covers_object_q_state:
  bounded_taylor64_covers_object_q_state source object_source_domain
      object_source_center object_source_center_gradient object_source_value
      object_source_gradient_bounds object_source_hessian /\
  bounded_taylor64_sqrt radii center_sqrt box_sqrt center_derivative
      box_derivative box_second_reciprocal source = SOME result ==>
  bounded_object_q_sqrt_certificate_exact object_source_center
      (bounded_interval64_object_q_cv center_sqrt) /\
  bounded_object_q_sqrt_certificate_exact object_source_value
      (bounded_interval64_object_q_cv box_sqrt) /\
  bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_add_cv
        (bounded_interval64_object_q_cv center_sqrt)
        (bounded_interval64_object_q_cv center_sqrt))
      (bounded_interval64_object_q_cv center_derivative) /\
  bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_add_cv
        (bounded_interval64_object_q_cv box_sqrt)
        (bounded_interval64_object_q_cv box_sqrt))
      (bounded_interval64_object_q_cv box_derivative) /\
  bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_mul_cv
        (bounded_object_q_interval_add_cv
          (bounded_interval64_object_q_cv box_sqrt)
          (bounded_interval64_object_q_cv box_sqrt))
        (bounded_object_q_interval_add_cv
          object_source_value object_source_value))
      (bounded_interval64_object_q_cv box_second_reciprocal) /\
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result
      (object_source_domain /\ T)
      (bounded_interval64_object_q_cv center_sqrt)
      (bounded_object_q_interval_list_scale_cv
        (bounded_interval64_object_q_cv center_derivative)
        object_source_center_gradient)
      (bounded_object_q_taylor_value_complete_cv
        (bounded_interval64_object_q_cv center_sqrt)
        (bounded_object_q_taylor_error_cv radii
          (bounded_object_q_interval_list_scale_cv
            (bounded_interval64_object_q_cv center_derivative)
            object_source_center_gradient)
          weights
          (bounded_object_q_taylor_unary_hessian_cv
            (bounded_interval64_object_q_cv box_derivative)
            (bounded_object_q_interval_neg_cv
              (bounded_interval64_object_q_cv box_second_reciprocal))
            object_source_gradient_bounds object_source_hessian)))
      (bounded_object_q_taylor_gradient_complete_cv radii
        (bounded_object_q_interval_list_scale_cv
          (bounded_interval64_object_q_cv center_derivative)
          object_source_center_gradient)
        (bounded_object_q_taylor_unary_hessian_cv
          (bounded_interval64_object_q_cv box_derivative)
          (bounded_object_q_interval_neg_cv
            (bounded_interval64_object_q_cv box_second_reciprocal))
          object_source_gradient_bounds object_source_hessian))
      (bounded_object_q_taylor_unary_hessian_cv
        (bounded_interval64_object_q_cv box_derivative)
        (bounded_object_q_interval_neg_cv
          (bounded_interval64_object_q_cv box_second_reciprocal))
        object_source_gradient_bounds object_source_hessian)
Proof
  strip_tac
  >> imp_res_tac bounded_taylor64_sqrt_reaches_object_q_unary_inputs
  >> rpt conj_tac
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >- asm_rewrite_tac []
  >> mp_tac
       (Q.INST
         [`source` |-> `source`,
          `object_source_domain` |-> `object_source_domain`,
          `object_source_center` |-> `object_source_center`,
          `object_source_center_gradient` |-> `object_source_center_gradient`,
          `object_source_value` |-> `object_source_value`,
          `object_source_gradient_bounds` |-> `object_source_gradient_bounds`,
          `object_source_hessian` |-> `object_source_hessian`,
          `result_domain` |-> `T`,
          `object_result_domain` |-> `T`,
          `center_result` |-> `center_sqrt`,
          `object_center_result` |->
            `bounded_interval64_object_q_cv center_sqrt`,
          `center_derivative` |-> `center_derivative`,
          `object_center_derivative` |->
            `bounded_interval64_object_q_cv center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `object_box_derivative` |->
            `bounded_interval64_object_q_cv box_derivative`,
          `box_second` |->
            `bounded_interval64_neg box_second_reciprocal`,
          `object_box_second` |->
            `bounded_object_q_interval_neg_cv
              (bounded_interval64_object_q_cv box_second_reciprocal)`,
          `radii` |-> `radii`, `result` |-> `result`]
         compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_taylor64_unary_covers_object_q_state)
  >> impl_tac
  >- asm_rewrite_tac []
  >> simp []
QED

val _ = export_theory ();
