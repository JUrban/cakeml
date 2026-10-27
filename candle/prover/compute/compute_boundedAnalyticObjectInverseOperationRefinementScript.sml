(*****************************************************************************
 * Operation-level object-q refinement for the scale-2^40 reciprocal lift.
 *
 * The executable reciprocal certificate accepts both positive and negative
 * sign-separated inputs.  Negating a valid negative certificate reduces it
 * to the already-proved positive source-rational contract.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectInverseOperationRefinement
Ancestors
  compute_boundedAnalyticObjectSqrtOperationRefinement
Libs
  bossLib preamble intLib

Theorem bounded_interval64_object_q_cv_neg:
  bounded_interval64_valid interval ==>
  bounded_interval64_object_q_cv (bounded_interval64_neg interval) =
    bounded_object_q_interval_neg_cv
      (bounded_interval64_object_q_cv interval)
Proof
  Cases_on `interval`
  >> rename1 `BoundedInterval64 lower upper`
  >> Cases_on `lower`
  >> Cases_on `upper`
  >> rename1
       `BoundedInterval64 (BoundedSigned64 lower_negative lower_magnitude)
          (BoundedSigned64 upper_negative upper_magnitude)`
  >> Cases_on `lower_negative`
  >> Cases_on `upper_negative`
  >> Cases_on `lower_magnitude = 0w`
  >> Cases_on `upper_magnitude = 0w`
  >> simp
       [compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_object_q_cv_def,
        compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_signed64_object_q_cv_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_interval_neg_cv_def,
        compute_boundedAnalyticObjectLinearRefinementTheory.bounded_object_q_neg_cv_def]
QED

Theorem bounded_interval64_inv_certificate_negative_negates:
  bounded_interval64_inv_certificate input output /\
  bounded_signed64_strict_negative (bounded_interval64_upper input) ==>
  bounded_interval64_inv_certificate
    (bounded_interval64_neg input) (bounded_interval64_neg output)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> rename1
       `bounded_interval64_inv_certificate
          (BoundedInterval64 input_lower input_upper)
          (BoundedInterval64 output_lower output_upper)`
  >> strip_tac
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> mp_tac
       (Q.INST
         [`input_lower` |-> `input_lower`,
          `input_upper` |-> `input_upper`,
          `output_lower` |-> `output_lower`,
          `output_upper` |-> `output_upper`]
         compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_negative_signs)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> Cases_on `input_lower`
  >> Cases_on `input_upper`
  >> Cases_on `output_lower`
  >> Cases_on `output_upper`
  >> fs
       [compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
        compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
        compute_boundedIntervalTheory.bounded_signed64_nonnegative_def,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct,
        compute_boundedIntervalAddTheory.bounded_interval64_neg_valid,
        compute_boundedIntervalTheory.bounded_interval64_valid_def,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_value,
        compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        wordsTheory.w2n_eq_0,
        LET_THM]
QED

Theorem bounded_interval64_inv_certificate_sign_split:
  bounded_interval64_inv_certificate input output ==>
  bounded_signed64_strict_positive (bounded_interval64_lower input) \/
  bounded_signed64_strict_negative (bounded_interval64_upper input)
Proof
  Cases_on `input`
  >> Cases_on `output`
  >> simp
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def,
        compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_signed64_strict_negative_neg_positive:
  bounded_signed64_strict_negative value ==>
  bounded_signed64_strict_positive (bounded_signed64_neg value)
Proof
  rw
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct,
        compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_value]
  >> intLib.ARITH_TAC
QED

Definition bounded_object_q_inv_certificate_exact_def:
  bounded_object_q_inv_certificate_exact input output <=>
    bounded_object_q_positive_inv_certificate_exact input output \/
    bounded_object_q_positive_inv_certificate_exact
      (bounded_object_q_interval_neg_cv input)
      (bounded_object_q_interval_neg_cv output)
End

Theorem bounded_interval64_inv_certificate_covers_object_q:
  bounded_interval64_covers_object_q input object_input /\
  bounded_interval64_inv_certificate input output ==>
  bounded_object_q_inv_certificate_exact object_input
    (bounded_interval64_object_q_cv output)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`input` |-> `input`, `output` |-> `output`]
         compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> Cases_on
       `bounded_signed64_strict_positive (bounded_interval64_lower input)`
  >- (rw [bounded_object_q_inv_certificate_exact_def]
      >> disj1_tac
      >> mp_tac
           (Q.INST
             [`input` |-> `input`,
              `output` |-> `output`,
              `object_input` |-> `object_input`]
             compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_positive_inv_certificate_covers_object_q)
      >> impl_tac >- asm_rewrite_tac []
      >> asm_rewrite_tac [])
  >> `bounded_signed64_strict_negative
         (bounded_interval64_upper input)` by
       (mp_tac
          (Q.INST
            [`input` |-> `input`, `output` |-> `output`]
            bounded_interval64_inv_certificate_sign_split)
        >> impl_tac >- asm_rewrite_tac []
        >> fs [])
  >> rw [bounded_object_q_inv_certificate_exact_def]
  >> disj2_tac
  >> `bounded_interval64_covers_object_q
        (bounded_interval64_neg input)
        (bounded_object_q_interval_neg_cv object_input)` by
       (irule
          compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q
        >> asm_rewrite_tac [])
  >> `bounded_interval64_inv_certificate
        (bounded_interval64_neg input)
        (bounded_interval64_neg output)` by
       (irule bounded_interval64_inv_certificate_negative_negates
        >> asm_rewrite_tac [])
  >> `bounded_signed64_strict_positive
        (bounded_interval64_lower (bounded_interval64_neg input))` by
       (Cases_on `input`
        >> fs
             [compute_boundedIntervalTheory.bounded_interval64_upper_def,
              compute_boundedIntervalAddTheory.bounded_interval64_neg_def,
              compute_boundedIntervalTheory.bounded_interval64_lower_def,
              bounded_signed64_strict_negative_neg_positive])
  >> `bounded_object_q_positive_inv_certificate_exact
        (bounded_object_q_interval_neg_cv object_input)
        (bounded_interval64_object_q_cv
          (bounded_interval64_neg output))` by
       (mp_tac
          (Q.INST
            [`input` |-> `bounded_interval64_neg input`,
             `output` |-> `bounded_interval64_neg output`,
             `object_input` |->
               `bounded_object_q_interval_neg_cv object_input`]
            compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_positive_inv_certificate_covers_object_q)
        >> impl_tac >- asm_rewrite_tac []
        >> asm_rewrite_tac [])
  >> `bounded_interval64_object_q_cv
        (bounded_interval64_neg output) =
      bounded_object_q_interval_neg_cv
        (bounded_interval64_object_q_cv output)` by
       (irule bounded_interval64_object_q_cv_neg
        >> asm_rewrite_tac [])
  >> qpat_x_assum
       `bounded_object_q_positive_inv_certificate_exact _
          (bounded_interval64_object_q_cv
            (bounded_interval64_neg output))` mp_tac
  >> asm_rewrite_tac []
QED

Theorem bounded_taylor64_inverse_refinement_trace:
  bounded_taylor64_inverse radii center_reciprocal box_reciprocal source =
      SOME result ==>
  ?source_domain center_value center_gradient value_bound gradient_bounds
      hessian center_square box_square box_cube box_second.
    source =
      BoundedTaylor64 source_domain center_value center_gradient value_bound
        gradient_bounds hessian /\
    bounded_interval64_inv_certificate center_value center_reciprocal /\
    bounded_interval64_inv_certificate value_bound box_reciprocal /\
    bounded_interval64_mul center_reciprocal center_reciprocal =
      SOME center_square /\
    bounded_interval64_mul box_reciprocal box_reciprocal =
      SOME box_square /\
    bounded_interval64_mul box_square box_reciprocal = SOME box_cube /\
    bounded_interval64_add box_cube box_cube = SOME box_second /\
    bounded_taylor64_unary_complete radii T center_reciprocal
      (bounded_interval64_neg center_square)
      (bounded_interval64_neg box_square) box_second source = SOME result
Proof
  Cases_on `source`
  >> rw [compute_boundedTaylorInverseTheory.bounded_taylor64_inverse_def]
  >> every_case_tac
  >> gvs []
  >> rpt (first_assum (irule_at Any))
QED

Theorem bounded_taylor64_inverse_reaches_object_q_unary_inputs:
  bounded_taylor64_covers_object_q_state source object_source_domain
      object_source_center object_source_center_gradient object_source_value
      object_source_gradient_bounds object_source_hessian /\
  bounded_taylor64_inverse radii center_reciprocal box_reciprocal source =
      SOME result ==>
  bounded_object_q_inv_certificate_exact object_source_center
      (bounded_interval64_object_q_cv center_reciprocal) /\
  bounded_object_q_inv_certificate_exact object_source_value
      (bounded_interval64_object_q_cv box_reciprocal) /\
  ?center_square box_square box_cube box_second.
    bounded_interval64_mul center_reciprocal center_reciprocal =
      SOME center_square /\
    bounded_interval64_mul box_reciprocal box_reciprocal =
      SOME box_square /\
    bounded_interval64_mul box_square box_reciprocal = SOME box_cube /\
    bounded_interval64_add box_cube box_cube = SOME box_second /\
    bounded_interval64_covers_object_q center_reciprocal
      (bounded_interval64_object_q_cv center_reciprocal) /\
    bounded_interval64_covers_object_q
      (bounded_interval64_neg center_square)
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          (bounded_interval64_object_q_cv center_reciprocal)
          (bounded_interval64_object_q_cv center_reciprocal))) /\
    bounded_interval64_covers_object_q
      (bounded_interval64_neg box_square)
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv
          (bounded_interval64_object_q_cv box_reciprocal)
          (bounded_interval64_object_q_cv box_reciprocal))) /\
    bounded_interval64_covers_object_q box_second
      (bounded_object_q_interval_add_cv
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_mul_cv
            (bounded_interval64_object_q_cv box_reciprocal)
            (bounded_interval64_object_q_cv box_reciprocal))
          (bounded_interval64_object_q_cv box_reciprocal))
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_mul_cv
            (bounded_interval64_object_q_cv box_reciprocal)
            (bounded_interval64_object_q_cv box_reciprocal))
          (bounded_interval64_object_q_cv box_reciprocal))) /\
    bounded_taylor64_unary_complete radii T center_reciprocal
      (bounded_interval64_neg center_square)
      (bounded_interval64_neg box_square) box_second source = SOME result
Proof
  strip_tac
  >> drule bounded_taylor64_inverse_refinement_trace
  >> disch_then
       (qx_choose_then `source_domain`
         (qx_choose_then `center_value`
           (qx_choose_then `center_gradient`
             (qx_choose_then `value_bound`
               (qx_choose_then `gradient_bounds`
                 (qx_choose_then `hessian`
                   (qx_choose_then `center_square`
                     (qx_choose_then `box_square`
                       (qx_choose_then `box_cube`
                         (qx_choose_then `box_second`
                           strip_assume_tac))))))))))
  >> fs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> `bounded_interval64_valid center_value /\
      bounded_interval64_valid center_reciprocal` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_valid value_bound /\
      bounded_interval64_valid box_reciprocal` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_covers_object_q center_reciprocal
        (bounded_interval64_object_q_cv center_reciprocal)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q box_reciprocal
        (bounded_interval64_object_q_cv box_reciprocal)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q center_square
        (bounded_object_q_interval_mul_cv
          (bounded_interval64_object_q_cv center_reciprocal)
          (bounded_interval64_object_q_cv center_reciprocal))` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q]
  >> `bounded_interval64_covers_object_q box_square
        (bounded_object_q_interval_mul_cv
          (bounded_interval64_object_q_cv box_reciprocal)
          (bounded_interval64_object_q_cv box_reciprocal))` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q]
  >> `bounded_interval64_covers_object_q box_cube
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_mul_cv
            (bounded_interval64_object_q_cv box_reciprocal)
            (bounded_interval64_object_q_cv box_reciprocal))
          (bounded_interval64_object_q_cv box_reciprocal))` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q]
  >> `bounded_interval64_covers_object_q box_second
        (bounded_object_q_interval_add_cv
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv
              (bounded_interval64_object_q_cv box_reciprocal)
              (bounded_interval64_object_q_cv box_reciprocal))
            (bounded_interval64_object_q_cv box_reciprocal))
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv
              (bounded_interval64_object_q_cv box_reciprocal)
              (bounded_interval64_object_q_cv box_reciprocal))
            (bounded_interval64_object_q_cv box_reciprocal)))` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q]
  >> rpt conj_tac
  >- metis_tac [bounded_interval64_inv_certificate_covers_object_q]
  >- metis_tac [bounded_interval64_inv_certificate_covers_object_q]
  >- asm_rewrite_tac []
  >- metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q]
  >- metis_tac
       [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q]
  >- asm_rewrite_tac []
  >> qpat_x_assum
       `bounded_taylor64_unary_complete _ _ _ _ _ _ source = _` mp_tac
  >> asm_rewrite_tac []
QED

Theorem bounded_taylor64_inverse_covers_object_q_state:
  bounded_taylor64_covers_object_q_state source object_source_domain
      object_source_center object_source_center_gradient object_source_value
      object_source_gradient_bounds object_source_hessian /\
  bounded_taylor64_inverse radii center_reciprocal box_reciprocal source =
      SOME result ==>
  bounded_object_q_inv_certificate_exact object_source_center
      (bounded_interval64_object_q_cv center_reciprocal) /\
  bounded_object_q_inv_certificate_exact object_source_value
      (bounded_interval64_object_q_cv box_reciprocal) /\
  ?weights.
    bounded_taylor_radius_pairs radii = SOME weights /\
    bounded_taylor64_covers_object_q_state result
      (object_source_domain /\ T)
      (bounded_interval64_object_q_cv center_reciprocal)
      (bounded_object_q_interval_list_scale_cv
        (bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv
            (bounded_interval64_object_q_cv center_reciprocal)
            (bounded_interval64_object_q_cv center_reciprocal)))
        object_source_center_gradient)
      (bounded_object_q_taylor_value_complete_cv
        (bounded_interval64_object_q_cv center_reciprocal)
        (bounded_object_q_taylor_error_cv radii
          (bounded_object_q_interval_list_scale_cv
            (bounded_object_q_interval_neg_cv
              (bounded_object_q_interval_mul_cv
                (bounded_interval64_object_q_cv center_reciprocal)
                (bounded_interval64_object_q_cv center_reciprocal)))
            object_source_center_gradient)
          weights
          (bounded_object_q_taylor_unary_hessian_cv
            (bounded_object_q_interval_neg_cv
              (bounded_object_q_interval_mul_cv
                (bounded_interval64_object_q_cv box_reciprocal)
                (bounded_interval64_object_q_cv box_reciprocal)))
            (bounded_object_q_interval_add_cv
              (bounded_object_q_interval_mul_cv
                (bounded_object_q_interval_mul_cv
                  (bounded_interval64_object_q_cv box_reciprocal)
                  (bounded_interval64_object_q_cv box_reciprocal))
                (bounded_interval64_object_q_cv box_reciprocal))
              (bounded_object_q_interval_mul_cv
                (bounded_object_q_interval_mul_cv
                  (bounded_interval64_object_q_cv box_reciprocal)
                  (bounded_interval64_object_q_cv box_reciprocal))
                (bounded_interval64_object_q_cv box_reciprocal)))
            object_source_gradient_bounds object_source_hessian)))
      (bounded_object_q_taylor_gradient_complete_cv radii
        (bounded_object_q_interval_list_scale_cv
          (bounded_object_q_interval_neg_cv
            (bounded_object_q_interval_mul_cv
              (bounded_interval64_object_q_cv center_reciprocal)
              (bounded_interval64_object_q_cv center_reciprocal)))
          object_source_center_gradient)
        (bounded_object_q_taylor_unary_hessian_cv
          (bounded_object_q_interval_neg_cv
            (bounded_object_q_interval_mul_cv
              (bounded_interval64_object_q_cv box_reciprocal)
              (bounded_interval64_object_q_cv box_reciprocal)))
          (bounded_object_q_interval_add_cv
            (bounded_object_q_interval_mul_cv
              (bounded_object_q_interval_mul_cv
                (bounded_interval64_object_q_cv box_reciprocal)
                (bounded_interval64_object_q_cv box_reciprocal))
              (bounded_interval64_object_q_cv box_reciprocal))
            (bounded_object_q_interval_mul_cv
              (bounded_object_q_interval_mul_cv
                (bounded_interval64_object_q_cv box_reciprocal)
                (bounded_interval64_object_q_cv box_reciprocal))
              (bounded_interval64_object_q_cv box_reciprocal)))
          object_source_gradient_bounds object_source_hessian))
      (bounded_object_q_taylor_unary_hessian_cv
        (bounded_object_q_interval_neg_cv
          (bounded_object_q_interval_mul_cv
            (bounded_interval64_object_q_cv box_reciprocal)
            (bounded_interval64_object_q_cv box_reciprocal)))
        (bounded_object_q_interval_add_cv
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv
              (bounded_interval64_object_q_cv box_reciprocal)
              (bounded_interval64_object_q_cv box_reciprocal))
            (bounded_interval64_object_q_cv box_reciprocal))
          (bounded_object_q_interval_mul_cv
            (bounded_object_q_interval_mul_cv
              (bounded_interval64_object_q_cv box_reciprocal)
              (bounded_interval64_object_q_cv box_reciprocal))
            (bounded_interval64_object_q_cv box_reciprocal)))
        object_source_gradient_bounds object_source_hessian)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`source` |-> `source`,
          `object_source_domain` |-> `object_source_domain`,
          `object_source_center` |-> `object_source_center`,
          `object_source_center_gradient` |-> `object_source_center_gradient`,
          `object_source_value` |-> `object_source_value`,
          `object_source_gradient_bounds` |-> `object_source_gradient_bounds`,
          `object_source_hessian` |-> `object_source_hessian`,
          `radii` |-> `radii`,
          `center_reciprocal` |-> `center_reciprocal`,
          `box_reciprocal` |-> `box_reciprocal`,
          `result` |-> `result`]
         bounded_taylor64_inverse_reaches_object_q_unary_inputs)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then strip_assume_tac
  >> rpt conj_tac
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
          `center_result` |-> `center_reciprocal`,
          `object_center_result` |->
            `bounded_interval64_object_q_cv center_reciprocal`,
          `center_derivative` |->
            `bounded_interval64_neg center_square`,
          `object_center_derivative` |->
            `bounded_object_q_interval_neg_cv
              (bounded_object_q_interval_mul_cv
                (bounded_interval64_object_q_cv center_reciprocal)
                (bounded_interval64_object_q_cv center_reciprocal))`,
          `box_derivative` |-> `bounded_interval64_neg box_square`,
          `object_box_derivative` |->
            `bounded_object_q_interval_neg_cv
              (bounded_object_q_interval_mul_cv
                (bounded_interval64_object_q_cv box_reciprocal)
                (bounded_interval64_object_q_cv box_reciprocal))`,
          `box_second` |-> `box_second`,
          `object_box_second` |->
            `bounded_object_q_interval_add_cv
              (bounded_object_q_interval_mul_cv
                (bounded_object_q_interval_mul_cv
                  (bounded_interval64_object_q_cv box_reciprocal)
                  (bounded_interval64_object_q_cv box_reciprocal))
                (bounded_interval64_object_q_cv box_reciprocal))
              (bounded_object_q_interval_mul_cv
                (bounded_object_q_interval_mul_cv
                  (bounded_interval64_object_q_cv box_reciprocal)
                  (bounded_interval64_object_q_cv box_reciprocal))
                (bounded_interval64_object_q_cv box_reciprocal))`,
          `radii` |-> `radii`, `result` |-> `result`]
         compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_taylor64_unary_covers_object_q_state)
  >> impl_tac
  >- asm_rewrite_tac []
  >> simp []
QED

val _ = export_theory ();
