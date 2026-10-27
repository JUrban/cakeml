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

val _ = export_theory ();
