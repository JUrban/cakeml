(*****************************************************************************
 * Joint fixed-word/object/production-dispatch adapters for certified
 * ordinary analytic instructions.
 *
 * The fixed-word evaluator is the authenticated witness checker.  Generic
 * word-to-object refinement supplies the mathematical analytic step, while
 * the canonical dispatcher adapters prove that the exact same certificate
 * packet is accepted by the production Candle evaluator.  Keeping all three
 * facts in one theorem prevents the later trace induction from choosing
 * unrelated semantic and evaluator witnesses.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchJointCertifiedStepInvariant
Ancestors
  compute_boundedCase16594Cell0WordDispatchPacketContracts
  compute_boundedCase16594ObjectDispatchCanonicalCertifiedStepInvariant
  compute_boundedAnalyticObjectCompleteDispatcherRefinement
Libs
  bossLib preamble intLib

Theorem bounded_interval64_inv_certificate_positive_output_implies_positive_input:
  bounded_interval64_inv_certificate input output /\
  bounded_signed64_strict_positive (bounded_interval64_lower output) ==>
  bounded_signed64_strict_positive (bounded_interval64_lower input)
Proof
  strip_tac
  >> drule
       compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_interval64_inv_certificate_sign_split
  >> strip_tac
  >> fs []
  >> Cases_on `input`
  >> Cases_on `output`
  >> fs
       [compute_boundedIntervalTheory.bounded_interval64_lower_def,
        compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> drule_all
       compute_boundedReciprocalCertificateTheory.bounded_interval64_inv_certificate_negative_signs
  >> fs
       [compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_positive_correct,
        compute_boundedReciprocalCertificateTheory.bounded_signed64_strict_negative_correct]
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_covers_object_q_valid_cv:
  bounded_interval64_covers_object_q word_interval object_interval ==>
  bounded_packed_q_interval_valid_cv object_interval
Proof
  rw
       [compute_boundedObjectIntervalRelationTheory.bounded_interval64_covers_object_q_def,
        compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> Cases_on `bounded_object_q_interval_ints object_interval`
  >> gvs []
  >> metis_tac
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_interval64_covers_object_q_ints_valid]
QED

Theorem bounded_interval64_object_q_cv_encoded:
  bounded_object_q_interval_encoded
    (bounded_interval64_object_q_cv (word_interval:bounded_interval64))
Proof
  simp
       [compute_boundedPackedObjectAcceptRefinementTheory.bounded_object_q_interval_encoded_def]
QED

Theorem bounded_object_q_square_certificate_exact_output_valid:
  bounded_object_q_square_certificate_exact source_input word_input output ==>
  bounded_packed_q_interval_valid_cv output
Proof
  rw
       [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_square_certificate_exact_def,
        compute_boundedPackedObjectSourceContractRefinementTheory.bounded_packed_q_interval_valid_cv_def]
  >> Cases_on `bounded_object_q_interval_ints word_input`
  >> Cases_on `bounded_object_q_interval_ints output`
  >> gvs
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
  >- (Cases_on `x` >> Cases_on `q` >> Cases_on `r` >> fs [])
  >> PairCases_on `x`
  >> PairCases_on `x'`
  >> fs
       [compute_boundedAnalyticObjectFusedProductRefinementTheory.bounded_int_fraction_interval_valid_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_positive_def,
        compute_boundedAnalyticObjectProductRefinementTheory.bounded_int_fraction_le_def]
QED

(* Keep the source fields visible.  The older existential refinement theorem
   deliberately hides them, which is too weak for proving that the semantic
   step consumes the exact authenticated runtime packet. *)
Theorem bounded_taylor64_atan_explicit_source_reaches_object_q_unary_inputs:
  bounded_taylor64_covers_object_q_state
      (BoundedTaylor64 word_domain word_center word_center_gradient
        word_box word_gradient_bounds word_hessian)
      object_domain object_center object_center_gradient object_box
      object_gradient_bounds object_hessian /\
  bounded_taylor64_atan radii lower_reciprocal upper_reciprocal
      center_derivative box_derivative
      (BoundedTaylor64 word_domain word_center word_center_gradient
        word_box word_gradient_bounds word_hessian) = SOME result ==>
  ?center_result center_square center_denominator box_square box_denominator
      box_derivative_square box_twice box_second_magnitude.
    bounded_interval64_atan_range word_center lower_reciprocal
      upper_reciprocal = SOME center_result /\
    bounded_object_q_interval_encloses
      (bounded_interval64_object_q_cv word_center) object_center /\
    bounded_object_q_square_certificate_exact object_center
      (bounded_interval64_object_q_cv word_center)
      (bounded_interval64_object_q_cv center_square) /\
    bounded_object_q_square_certificate_exact object_box
      (bounded_interval64_object_q_cv word_box)
      (bounded_interval64_object_q_cv box_square) /\
    bounded_object_q_inv_certificate_exact
      (bounded_object_q_atan_denominator_cv
        (bounded_interval64_object_q_cv center_square))
      (bounded_interval64_object_q_cv center_derivative) /\
    bounded_object_q_inv_certificate_exact
      (bounded_object_q_atan_denominator_cv
        (bounded_interval64_object_q_cv box_square))
      (bounded_interval64_object_q_cv box_derivative) /\
    bounded_object_q_square_certificate_exact
      (bounded_interval64_object_q_cv box_derivative)
      (bounded_interval64_object_q_cv box_derivative)
      (bounded_interval64_object_q_cv box_derivative_square) /\
    bounded_interval64_square word_center = SOME center_square /\
    bounded_interval64_add bounded_atan_one center_square =
      SOME center_denominator /\
    bounded_interval64_square word_box = SOME box_square /\
    bounded_interval64_add bounded_atan_one box_square =
      SOME box_denominator /\
    bounded_interval64_square box_derivative =
      SOME box_derivative_square /\
    bounded_interval64_add word_box word_box = SOME box_twice /\
    bounded_interval64_mul box_twice box_derivative_square =
      SOME box_second_magnitude /\
    bounded_interval64_covers_object_q center_result
      (bounded_interval64_object_q_cv center_result) /\
    bounded_interval64_covers_object_q center_derivative
      (bounded_interval64_object_q_cv center_derivative) /\
    bounded_interval64_covers_object_q box_derivative
      (bounded_interval64_object_q_cv box_derivative) /\
    bounded_interval64_covers_object_q
      (bounded_interval64_neg box_second_magnitude)
      (bounded_object_q_atan_second_cv object_box
        (bounded_interval64_object_q_cv box_derivative_square)) /\
    bounded_taylor64_unary_complete radii T center_result
      center_derivative box_derivative
      (bounded_interval64_neg box_second_magnitude)
      (BoundedTaylor64 word_domain word_center word_center_gradient
        word_box word_gradient_bounds word_hessian) = SOME result
Proof
  strip_tac
  >> drule
       compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_taylor64_atan_refinement_trace
  >> disch_then
       (qx_choose_then `source_domain`
         (qx_choose_then `actual_center`
           (qx_choose_then `actual_center_gradient`
             (qx_choose_then `actual_box`
               (qx_choose_then `actual_gradient_bounds`
                 (qx_choose_then `actual_hessian`
                   (qx_choose_then `center_result`
                     (qx_choose_then `center_square`
                       (qx_choose_then `center_denominator`
                         (qx_choose_then `box_square`
                           (qx_choose_then `box_denominator`
                             (qx_choose_then `box_derivative_square`
                               (qx_choose_then `box_twice`
                                 (qx_choose_then `box_second_magnitude`
                                   strip_assume_tac))))))))))))))
  >> gvs []
  >> fs
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> `bounded_interval64_valid actual_center /\
      bounded_interval64_valid center_result` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_atan_range_valid_components]
  >> `bounded_interval64_valid actual_box` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_square_some_valid_input]
  >> `bounded_interval64_valid center_square` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_add_some_valid_components]
  >> `bounded_interval64_valid box_square` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_add_some_valid_components]
  >> `bounded_interval64_valid center_denominator /\
      bounded_interval64_valid center_derivative` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_valid box_denominator /\
      bounded_interval64_valid box_derivative` by
       metis_tac
         [compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_inv_certificate_valid_components]
  >> `bounded_interval64_valid box_derivative_square` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_mul_some_valid_inputs]
  >> `bounded_interval64_covers_object_q center_square
        (bounded_interval64_object_q_cv center_square) /\
      bounded_interval64_covers_object_q box_square
        (bounded_interval64_object_q_cv box_square) /\
      bounded_interval64_covers_object_q center_derivative
        (bounded_interval64_object_q_cv center_derivative) /\
      bounded_interval64_covers_object_q box_derivative
        (bounded_interval64_object_q_cv box_derivative) /\
      bounded_interval64_covers_object_q box_derivative_square
        (bounded_interval64_object_q_cv box_derivative_square) /\
      bounded_interval64_covers_object_q center_result
        (bounded_interval64_object_q_cv center_result)` by
       metis_tac
         [compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q]
  >> `bounded_interval64_covers_object_q center_denominator
        (bounded_object_q_atan_denominator_cv
          (bounded_interval64_object_q_cv center_square)) /\
      bounded_interval64_covers_object_q box_denominator
        (bounded_object_q_atan_denominator_cv
          (bounded_interval64_object_q_cv box_square))` by
       (rw
          [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_denominator_cv_def]
        >> metis_tac
             [compute_boundedAnalyticObjectRefinementTheory.bounded_atan_one_covers_object_q_one,
              compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q])
  >> `bounded_interval64_covers_object_q box_twice
        (bounded_object_q_interval_add_cv object_box object_box)` by
       metis_tac
         [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_add_covers_object_q]
  >> `bounded_interval64_covers_object_q box_second_magnitude
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv object_box object_box)
          (bounded_interval64_object_q_cv box_derivative_square))` by
       metis_tac
         [compute_boundedAnalyticObjectProductRefinementTheory.bounded_interval64_mul_covers_object_q]
  >> `bounded_interval64_covers_object_q
        (bounded_interval64_neg box_second_magnitude)
        (bounded_object_q_atan_second_cv object_box
          (bounded_interval64_object_q_cv box_derivative_square))` by
       (rw
          [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_second_cv_def]
        >> metis_tac
             [compute_boundedAnalyticObjectLinearRefinementTheory.bounded_interval64_neg_covers_object_q])
  >> `bounded_object_q_interval_encloses
        (bounded_interval64_object_q_cv actual_center) object_center` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_covers_object_q_encloses]
  >> `bounded_object_q_square_certificate_exact object_center
        (bounded_interval64_object_q_cv actual_center)
        (bounded_interval64_object_q_cv center_square) /\
      bounded_object_q_square_certificate_exact object_box
        (bounded_interval64_object_q_cv actual_box)
        (bounded_interval64_object_q_cv box_square)` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_square_own_object_q_exact]
  >> `bounded_object_q_square_certificate_exact
        (bounded_interval64_object_q_cv box_derivative)
        (bounded_interval64_object_q_cv box_derivative)
        (bounded_interval64_object_q_cv box_derivative_square)` by
       metis_tac
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_interval64_square_own_object_q_exact]
  >> `bounded_object_q_inv_certificate_exact
        (bounded_object_q_atan_denominator_cv
          (bounded_interval64_object_q_cv center_square))
        (bounded_interval64_object_q_cv center_derivative) /\
      bounded_object_q_inv_certificate_exact
        (bounded_object_q_atan_denominator_cv
          (bounded_interval64_object_q_cv box_square))
        (bounded_interval64_object_q_cv box_derivative)` by
       metis_tac
         [compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_interval64_inv_certificate_covers_object_q]
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_joint_sqrt_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Sqrt /\
  bounded_analytic64_state_covers_object_q
    (word_stack,
     BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
       center_derivative box_derivative box_second_reciprocal::
       semantic_certificate_rest)
    (semantic_stack,
     BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
       center_derivative box_derivative box_second_reciprocal::
       semantic_certificate_rest) /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes BoundedAnalytic64Sqrt
    (word_stack,
     BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
       center_derivative box_derivative box_second_reciprocal::
       semantic_certificate_rest) = SOME word_next /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack semantic_stack
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Sqrt
      (semantic_stack,
       BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::
         semantic_certificate_rest)
      semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      runtime_center_boxes runtime_outer_boxes
      (bounded_object_q_cv_list runtime_radii) (Num 0)
      (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        ([bounded_interval64_object_q_cv center_sqrt;
          bounded_interval64_object_q_cv box_sqrt;
          bounded_interval64_object_q_cv center_derivative;
          bounded_interval64_object_q_cv box_derivative;
          bounded_interval64_object_q_cv box_second_reciprocal] ++
         runtime_certificate_rest))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificate_rest
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`source` |-> `source`, `prepared` |-> `BoundedAnalytic64Sqrt`,
          `word_state` |->
            `(word_stack,
              BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
                center_derivative box_derivative box_second_reciprocal::
                semantic_certificate_rest)`,
          `object_state` |->
            `(semantic_stack,
              BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
                center_derivative box_derivative box_second_reciprocal::
                semantic_certificate_rest)`,
          `center_environment` |-> `word_center_boxes`,
          `object_center_environment` |-> `semantic_center_boxes`,
          `box_environment` |-> `word_outer_boxes`,
          `object_box_environment` |-> `semantic_outer_boxes`,
          `radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `word_next` |-> `word_next`]
         compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_analytic64_complete_dispatch_refines_object_q)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `semantic_next` strip_assume_tac)
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `source` |-> `source`, `semantic_stack` |-> `semantic_stack`,
          `semantic_certificates` |->
            `BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
               center_derivative box_derivative box_second_reciprocal::
             semantic_certificate_rest`,
          `semantic_next` |-> `semantic_next`,
          `runtime_stack` |-> `runtime_stack`,
          `center_boxes` |-> `runtime_center_boxes`,
          `outer_boxes` |-> `runtime_outer_boxes`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `center_sqrt` |-> `center_sqrt`, `box_sqrt` |-> `box_sqrt`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `box_second_reciprocal` |-> `box_second_reciprocal`,
          `semantic_certificate_rest` |-> `semantic_certificate_rest`,
          `runtime_certificate_rest` |-> `runtime_certificate_rest`]
         compute_boundedCase16594ObjectDispatchCanonicalCertifiedStepInvariantTheory.bounded_case16594_object_canonical_sqrt_step_eval_above)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `next_runtime_stack` strip_assume_tac)
  >> qexists_tac `semantic_next`
  >> qexists_tac `next_runtime_stack`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_positive_inverse_witnesses:
  bounded_analytic64_state_covers_object_q
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       certificate_rest)
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_box object_gradient_bounds object_hessian::object_rest,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       certificate_rest) /\
  bounded_analytic64_program_step radii center_environment box_environment
    BoundedAnalytic64Inverse
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       certificate_rest) = SOME word_next /\
  bounded_signed64_strict_positive
    (bounded_interval64_lower center_reciprocal) /\
  bounded_signed64_strict_positive
    (bounded_interval64_lower box_reciprocal)
  ==>
  bounded_object_q_positive_inv_certificate_exact object_center
    (bounded_interval64_object_q_cv center_reciprocal) /\
  bounded_object_q_positive_inv_certificate_exact object_box
    (bounded_interval64_object_q_cv box_reciprocal)
Proof
  strip_tac
  >> fs
       [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> Cases_on
       `bounded_taylor64_inverse radii center_reciprocal box_reciprocal
          (BoundedTaylor64 word_domain word_center word_center_gradient
            word_box word_gradient_bounds word_hessian)`
  >> gvs []
  >> drule
       compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_taylor64_inverse_refinement_trace
  >> strip_tac
  >> gvs
       [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
        compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
        compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def,
        LIST_REL_def]
  >> metis_tac
       [bounded_interval64_inv_certificate_positive_output_implies_positive_input,
        compute_boundedAnalyticObjectReciprocalRefinementTheory.bounded_interval64_positive_inv_certificate_covers_object_q]
QED

Theorem bounded_case16594_object_joint_inverse_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Inverse /\
  bounded_analytic64_state_covers_object_q
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       semantic_certificate_rest)
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_box object_gradient_bounds object_hessian::semantic_tail,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       semantic_certificate_rest) /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes BoundedAnalytic64Inverse
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
       semantic_certificate_rest) = SOME word_next /\
  bounded_signed64_strict_positive
    (bounded_interval64_lower center_reciprocal) /\
  bounded_signed64_strict_positive
    (bounded_interval64_lower box_reciprocal) /\
  bounded_object_q_taylor_stack_runtime_refines runtime_stack
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_box object_gradient_bounds object_hessian::semantic_tail)
  ==>
  ?semantic_next next_runtime_stack.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source
      BoundedAnalytic64Inverse
      (BoundedObjectQTaylor object_domain object_center object_center_gradient
         object_box object_gradient_bounds object_hessian::semantic_tail,
       BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
         semantic_certificate_rest)
      semantic_next /\
    bounded_analytic64_state_covers_object_q word_next semantic_next /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      runtime_center_boxes runtime_outer_boxes
      (bounded_object_q_cv_list runtime_radii) (Num 0)
      (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        ([bounded_interval64_object_q_cv center_reciprocal;
          bounded_interval64_object_q_cv box_reciprocal] ++
         runtime_certificate_rest))
      (bounded_object_q_cv_list runtime_stack)
      (bounded_object_q_cv_list next_runtime_stack)
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines next_runtime_stack
      (FST semantic_next) /\
    SND semantic_next = semantic_certificate_rest
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`source` |-> `source`, `prepared` |-> `BoundedAnalytic64Inverse`,
          `word_state` |->
            `(BoundedTaylor64 word_domain word_center word_center_gradient
                word_box word_gradient_bounds word_hessian::word_rest,
              BoundedAnalytic64InverseCertificate center_reciprocal
                box_reciprocal::semantic_certificate_rest)`,
          `object_state` |->
            `(BoundedObjectQTaylor object_domain object_center
                object_center_gradient object_box object_gradient_bounds
                object_hessian::semantic_tail,
              BoundedAnalytic64InverseCertificate center_reciprocal
                box_reciprocal::semantic_certificate_rest)`,
          `center_environment` |-> `word_center_boxes`,
          `object_center_environment` |-> `semantic_center_boxes`,
          `box_environment` |-> `word_outer_boxes`,
          `object_box_environment` |-> `semantic_outer_boxes`,
          `radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `word_next` |-> `word_next`]
         compute_boundedAnalyticObjectCompleteDispatcherRefinementTheory.bounded_analytic64_complete_dispatch_refines_object_q)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `semantic_next` strip_assume_tac)
  >> `bounded_object_q_positive_inv_certificate_exact object_center
        (bounded_interval64_object_q_cv center_reciprocal) /\
      bounded_object_q_positive_inv_certificate_exact object_box
        (bounded_interval64_object_q_cv box_reciprocal)` by
       metis_tac [bounded_case16594_object_positive_inverse_witnesses]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`, `weights` |-> `weights`,
          `source` |-> `source`, `object_domain` |-> `object_domain`,
          `object_center` |-> `object_center`,
          `object_center_gradient` |-> `object_center_gradient`,
          `object_value` |-> `object_box`,
          `object_gradient_bounds` |-> `object_gradient_bounds`,
          `object_hessian` |-> `object_hessian`,
          `semantic_tail` |-> `semantic_tail`,
          `semantic_certificate_rest` |-> `semantic_certificate_rest`,
          `semantic_next` |-> `semantic_next`,
          `runtime_stack` |-> `runtime_stack`,
          `center_boxes` |-> `runtime_center_boxes`,
          `outer_boxes` |-> `runtime_outer_boxes`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `center_reciprocal` |-> `center_reciprocal`,
          `box_reciprocal` |-> `box_reciprocal`,
          `runtime_certificate_rest` |-> `runtime_certificate_rest`]
         compute_boundedCase16594ObjectDispatchCanonicalCertifiedStepInvariantTheory.bounded_case16594_object_canonical_inverse_step_eval_above)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `next_runtime_stack` strip_assume_tac)
  >> qexists_tac `semantic_next`
  >> qexists_tac `next_runtime_stack`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_joint_atan_step_eval_above:
  EVERY bounded_object_q_encoded runtime_radii /\
  LENGTH runtime_radii = 6 /\
  bounded_taylor_radius_pairs semantic_radii = SOME weights /\
  LIST_REL bounded_case10173_q_cv_equiv runtime_radii
    (MAP bounded_word64_object_q_cv semantic_radii) /\
  bounded_analytic_instruction_refines 6 source BoundedAnalytic64Atan /\
  bounded_analytic64_state_covers_object_q
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
       center_derivative box_derivative::semantic_certificate_rest)
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_box object_gradient_bounds object_hessian::semantic_tail,
     BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
       center_derivative box_derivative::semantic_certificate_rest) /\
  LIST_REL bounded_interval64_covers_object_q
    word_center_boxes semantic_center_boxes /\
  LIST_REL bounded_interval64_covers_object_q
    word_outer_boxes semantic_outer_boxes /\
  bounded_analytic64_program_step semantic_radii word_center_boxes
    word_outer_boxes BoundedAnalytic64Atan
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
       center_derivative box_derivative::semantic_certificate_rest) =
      SOME word_next /\
  bounded_analytic64_runtime_certificate_packet BoundedAnalytic64Atan
    (BoundedTaylor64 word_domain word_center word_center_gradient
       word_box word_gradient_bounds word_hessian::word_rest,
     BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
       center_derivative box_derivative::semantic_certificate_rest) =
      SOME
        [center_input;box_input;center_result;center_square;
         center_derivative;box_square;box_derivative;
         box_derivative_square] /\
  bounded_case16594_object_atan_fixed_pure_contract
    (bounded_interval64_object_q_cv center_input)
    (bounded_interval64_object_q_cv box_input)
    (bounded_interval64_object_q_cv center_result)
    (bounded_interval64_object_q_cv center_square)
    (bounded_interval64_object_q_cv center_derivative)
    (bounded_interval64_object_q_cv box_square)
    (bounded_interval64_object_q_cv box_derivative)
    (bounded_interval64_object_q_cv box_derivative_square) /\
  bounded_object_q_taylor_stack_runtime_refines
    (runtime_head::runtime_tail)
    (BoundedObjectQTaylor object_domain object_center object_center_gradient
       object_box object_gradient_bounds object_hessian::semantic_tail)
  ==>
  ?runtime_result.
    bounded_object_q_analytic_step semantic_radii weights
      semantic_center_boxes semantic_outer_boxes source BoundedAnalytic64Atan
      (BoundedObjectQTaylor object_domain object_center object_center_gradient
         object_box object_gradient_bounds object_hessian::semantic_tail,
       BoundedAnalytic64AtanCertificate lower_reciprocal upper_reciprocal
         center_derivative box_derivative::semantic_certificate_rest)
      (bounded_object_q_taylor_atan semantic_radii weights
         (bounded_interval64_object_q_cv center_result)
         (bounded_interval64_object_q_cv center_derivative)
         (bounded_interval64_object_q_cv box_derivative)
         (bounded_interval64_object_q_cv box_derivative_square)
         (BoundedObjectQTaylor object_domain object_center
           object_center_gradient object_box object_gradient_bounds
           object_hessian)::semantic_tail,
       semantic_certificate_rest) /\
    bounded_analytic64_state_covers_object_q word_next
      (bounded_object_q_taylor_atan semantic_radii weights
         (bounded_interval64_object_q_cv center_result)
         (bounded_interval64_object_q_cv center_derivative)
         (bounded_interval64_object_q_cv box_derivative)
         (bounded_interval64_object_q_cv box_derivative_square)
         (BoundedObjectQTaylor object_domain object_center
           object_center_gradient object_box object_gradient_bounds
           object_hessian)::semantic_tail,
       semantic_certificate_rest) /\
    bounded_case16594_object_dispatch_step_eval_above 524405
      runtime_center_boxes runtime_outer_boxes
      (bounded_object_q_cv_list runtime_radii) (Num 0)
      (bounded_case16594_analytic_instruction_cv source)
      (bounded_object_q_cv_list
        ([bounded_interval64_object_q_cv center_input;
          bounded_interval64_object_q_cv box_input;
          bounded_interval64_object_q_cv center_result;
          bounded_interval64_object_q_cv center_square;
          bounded_interval64_object_q_cv center_derivative;
          bounded_interval64_object_q_cv box_square;
          bounded_interval64_object_q_cv box_derivative;
          bounded_interval64_object_q_cv box_derivative_square] ++
         runtime_certificate_rest))
      (bounded_object_q_cv_list (runtime_head::runtime_tail))
      (bounded_object_q_cv_list (runtime_result::runtime_tail))
      (bounded_object_q_cv_list runtime_certificate_rest) /\
    bounded_object_q_taylor_stack_runtime_refines
      (runtime_result::runtime_tail)
      (bounded_object_q_taylor_atan semantic_radii weights
         (bounded_interval64_object_q_cv center_result)
         (bounded_interval64_object_q_cv center_derivative)
         (bounded_interval64_object_q_cv box_derivative)
         (bounded_interval64_object_q_cv box_derivative_square)
         (BoundedObjectQTaylor object_domain object_center
           object_center_gradient object_box object_gradient_bounds
           object_hessian)::semantic_tail)
Proof
  strip_tac
  >> `bounded_taylor64_covers_object_q
        (BoundedTaylor64 word_domain word_center word_center_gradient
          word_box word_gradient_bounds word_hessian)
        (BoundedObjectQTaylor object_domain object_center
          object_center_gradient object_box object_gradient_bounds
          object_hessian) /\
      bounded_taylor64_stack_covers_object_q word_rest semantic_tail` by
       fs
         [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> fs
       [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> Cases_on
       `bounded_taylor64_atan semantic_radii lower_reciprocal
          upper_reciprocal center_derivative box_derivative
          (BoundedTaylor64 word_domain word_center word_center_gradient
            word_box word_gradient_bounds word_hessian)`
  >> gvs []
  >> mp_tac
       (Q.INST
         [`word_domain` |-> `word_domain`, `word_center` |-> `word_center`,
          `word_center_gradient` |-> `word_center_gradient`,
          `word_box` |-> `word_box`,
          `word_gradient_bounds` |-> `word_gradient_bounds`,
          `word_hessian` |-> `word_hessian`,
          `object_domain` |-> `object_domain`,
          `object_center` |-> `object_center`,
          `object_center_gradient` |-> `object_center_gradient`,
          `object_box` |-> `object_box`,
          `object_gradient_bounds` |-> `object_gradient_bounds`,
          `object_hessian` |-> `object_hessian`,
          `radii` |-> `semantic_radii`,
          `lower_reciprocal` |-> `lower_reciprocal`,
          `upper_reciprocal` |-> `upper_reciprocal`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`, `result` |-> `x`]
         bounded_taylor64_atan_explicit_source_reaches_object_q_unary_inputs)
  >> impl_tac
  >- fs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
  >> disch_then
       (qx_choose_then `actual_center_result`
         (qx_choose_then `actual_center_square`
           (qx_choose_then `center_denominator`
             (qx_choose_then `actual_box_square`
               (qx_choose_then `box_denominator`
                 (qx_choose_then `actual_box_derivative_square`
                   (qx_choose_then `box_twice`
                     (qx_choose_then `box_second_magnitude`
                       strip_assume_tac))))))))
  >> gvs
       [compute_boundedAnalyticRuntimeCertificateTraceTheory.bounded_analytic64_runtime_certificate_packet_def]
  >> `bounded_packed_q_interval_valid_cv
        (bounded_interval64_object_q_cv actual_center_result) /\
      bounded_packed_q_interval_valid_cv
        (bounded_interval64_object_q_cv center_derivative) /\
      bounded_packed_q_interval_valid_cv
        (bounded_interval64_object_q_cv box_derivative) /\
      bounded_packed_q_interval_valid_cv
        (bounded_interval64_object_q_cv actual_box_derivative_square)` by
       metis_tac
         [bounded_interval64_covers_object_q_valid_cv,
          bounded_object_q_square_certificate_exact_output_valid]
  >> `bounded_object_q_interval_encoded
        (bounded_interval64_object_q_cv center_input) /\
      bounded_object_q_interval_encoded
        (bounded_interval64_object_q_cv box_input)` by
       simp [bounded_interval64_object_q_cv_encoded]
  >> `bounded_object_q_interval_encloses
        (bounded_interval64_object_q_cv box_input) object_box` by
       fs
         [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_square_certificate_exact_def]
  >> mp_tac
       (Q.INST
         [`source` |->
            `BoundedTaylor64 word_domain center_input word_center_gradient
               box_input word_gradient_bounds word_hessian`,
          `object_source_domain` |-> `object_domain`,
          `object_source_center` |-> `object_center`,
          `object_source_center_gradient` |-> `object_center_gradient`,
          `object_source_value` |-> `object_box`,
          `object_source_gradient_bounds` |-> `object_gradient_bounds`,
          `object_source_hessian` |-> `object_hessian`,
          `result_domain` |-> `T`, `object_result_domain` |-> `T`,
          `center_result` |-> `actual_center_result`,
          `object_center_result` |->
            `bounded_interval64_object_q_cv actual_center_result`,
          `center_derivative` |-> `center_derivative`,
          `object_center_derivative` |->
            `bounded_interval64_object_q_cv center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `object_box_derivative` |->
            `bounded_interval64_object_q_cv box_derivative`,
          `box_second` |-> `bounded_interval64_neg box_second_magnitude`,
          `object_box_second` |->
            `bounded_object_q_atan_second_cv object_box
               (bounded_interval64_object_q_cv actual_box_derivative_square)`,
          `radii` |-> `semantic_radii`, `result` |-> `x`]
         compute_boundedAnalyticObjectUnaryRefinementTheory.bounded_taylor64_unary_covers_object_q_state)
  >> impl_tac
  >- fs
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
  >> disch_then (qx_choose_then `result_weights` strip_assume_tac)
  >> gvs []
  >> `bounded_taylor64_covers_object_q x
        (bounded_object_q_taylor_atan semantic_radii result_weights
          (bounded_interval64_object_q_cv actual_center_result)
          (bounded_interval64_object_q_cv center_derivative)
          (bounded_interval64_object_q_cv box_derivative)
          (bounded_interval64_object_q_cv actual_box_derivative_square)
          (BoundedObjectQTaylor object_domain object_center
            object_center_gradient object_box object_gradient_bounds
            object_hessian))` by
       fs
         [compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_atan_def,
          compute_boundedAnalyticObjectProgramSemanticsTheory.bounded_object_q_taylor_unary_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
  >> `bounded_analytic64_state_covers_object_q
        (x::word_rest,semantic_certificate_rest)
        (bounded_object_q_taylor_atan semantic_radii result_weights
           (bounded_interval64_object_q_cv actual_center_result)
           (bounded_interval64_object_q_cv center_derivative)
           (bounded_interval64_object_q_cv box_derivative)
           (bounded_interval64_object_q_cv actual_box_derivative_square)
           (BoundedObjectQTaylor object_domain object_center
             object_center_gradient object_box object_gradient_bounds
             object_hessian)::semantic_tail,
         semantic_certificate_rest)` by
       fs
         [compute_boundedAnalyticObjectProgramStepRefinementTheory.bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`runtime_radii` |-> `runtime_radii`,
          `semantic_radii` |-> `semantic_radii`,
          `weights` |-> `result_weights`,
          `source` |-> `source`,
          `semantic_state` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_box object_gradient_bounds
               object_hessian`,
          `semantic_tail` |-> `semantic_tail`,
          `lower_reciprocal` |-> `lower_reciprocal`,
          `upper_reciprocal` |-> `upper_reciprocal`,
          `center_input` |-> `center_input`, `box_input` |-> `box_input`,
          `center_result` |-> `actual_center_result`,
          `center_square` |-> `actual_center_square`,
          `center_derivative` |-> `center_derivative`,
          `box_square` |-> `actual_box_square`,
          `box_derivative` |-> `box_derivative`,
          `box_derivative_square` |-> `actual_box_derivative_square`,
          `semantic_certificate_rest` |-> `semantic_certificate_rest`,
          `runtime_head` |-> `runtime_head`,
          `runtime_tail` |-> `runtime_tail`,
          `center_boxes` |-> `runtime_center_boxes`,
          `outer_boxes` |-> `runtime_outer_boxes`,
          `semantic_center_boxes` |-> `semantic_center_boxes`,
          `semantic_outer_boxes` |-> `semantic_outer_boxes`,
          `runtime_certificate_rest` |-> `runtime_certificate_rest`]
         compute_boundedCase16594ObjectDispatchCanonicalCertifiedStepInvariantTheory.bounded_case16594_object_canonical_atan_step_eval_above)
  >> impl_tac
  >- asm_simp_tac (srw_ss())
       [compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_center_def,
        compute_boundedObjectTaylorEquivalenceTheory.bounded_object_q_taylor_value_bound_def]
  >> disch_then (qx_choose_then `runtime_result` strip_assume_tac)
  >> qexists_tac `runtime_result`
  >> fs []
QED

val _ = export_theory ();
