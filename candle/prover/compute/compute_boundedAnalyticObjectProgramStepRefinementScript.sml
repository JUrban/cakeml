(*****************************************************************************
 * Object-q stack semantics for the ordinary outer analytic executor.
 *
 * Certificates remain the exact untrusted word records consumed by the real
 * evaluator.  The object step checks their rational meaning and constructs
 * the corresponding complete Taylor state.  Recognized delta instructions
 * are intentionally outside this relation and remain a separate proof gate.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectProgramStepRefinement
Ancestors
  compute_boundedAnalyticObjectProgramSemantics
Libs
  bossLib preamble

Definition bounded_analytic64_state_covers_object_q_def:
  bounded_analytic64_state_covers_object_q
      (word_stack,word_certificates)
      (object_stack,object_certificates) <=>
    bounded_taylor64_stack_covers_object_q word_stack object_stack /\
    word_certificates = object_certificates
End

Definition bounded_object_q_analytic_ordinary_step_def:
  bounded_object_q_analytic_ordinary_step radii weights center_environment
      box_environment (instruction:bounded_analytic_instruction)
      (object_state:bounded_object_q_taylor_state list #
        bounded_analytic64_certificate list)
      (object_next:bounded_object_q_taylor_state list #
        bounded_analytic64_certificate list) <=>
    case (instruction,object_state) of
    | (BoundedAnalyticPolynomial program,(stack,certificates)) =>
        ?result.
          bounded_object_q_poly_run radii weights center_environment
            box_environment program [] = SOME [result] /\
          object_next = (result::stack,certificates)
    | (BoundedAnalyticSqrt,
        (BoundedObjectQTaylor object_domain object_center object_center_gradient
           object_value object_gradient_bounds object_hessian::rest,
         BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
           center_derivative box_derivative box_second_reciprocal::
           certificate_rest)) =>
        bounded_object_q_sqrt_certificate_exact object_center
          (bounded_interval64_object_q_cv center_sqrt) /\
        bounded_object_q_sqrt_certificate_exact object_value
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
            (bounded_object_q_interval_add_cv object_value object_value))
          (bounded_interval64_object_q_cv box_second_reciprocal) /\
        object_next =
          (bounded_object_q_taylor_sqrt radii weights
             (bounded_interval64_object_q_cv center_sqrt)
             (bounded_interval64_object_q_cv center_derivative)
             (bounded_interval64_object_q_cv box_derivative)
             (bounded_interval64_object_q_cv box_second_reciprocal)
             (BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_value object_gradient_bounds
               object_hessian)::rest,
           certificate_rest)
    | (BoundedAnalyticNeg,(value::rest,certificates)) =>
        object_next =
          (bounded_object_q_taylor_neg radii weights value::rest,certificates)
    | (BoundedAnalyticAdd,(right::left::rest,certificates)) =>
        object_next =
          (bounded_object_q_taylor_add radii weights left right::rest,
           certificates)
    | (BoundedAnalyticMul,(right::left::rest,certificates)) =>
        object_next =
          (bounded_object_q_taylor_mul radii weights left right::rest,
           certificates)
    | (BoundedAnalyticSquare,(value::rest,certificates)) =>
        object_next =
          (bounded_object_q_taylor_mul radii weights value value::rest,
           certificates)
    | (BoundedAnalyticInverse,
        (BoundedObjectQTaylor object_domain object_center object_center_gradient
           object_value object_gradient_bounds object_hessian::rest,
         BoundedAnalytic64InverseCertificate center_reciprocal
           box_reciprocal::certificate_rest)) =>
        bounded_object_q_inv_certificate_exact object_center
          (bounded_interval64_object_q_cv center_reciprocal) /\
        bounded_object_q_inv_certificate_exact object_value
          (bounded_interval64_object_q_cv box_reciprocal) /\
        object_next =
          (bounded_object_q_taylor_inverse radii weights
             (bounded_interval64_object_q_cv center_reciprocal)
             (bounded_interval64_object_q_cv box_reciprocal)
             (BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_value object_gradient_bounds
               object_hessian)::rest,
           certificate_rest)
    | (BoundedAnalyticAtan,
        (BoundedObjectQTaylor object_domain object_center object_center_gradient
           object_value object_gradient_bounds object_hessian::rest,
         BoundedAnalytic64AtanCertificate center_lower_reciprocal
           center_upper_reciprocal center_derivative box_derivative::
           certificate_rest)) =>
        ?center_value value_bound center_result center_square box_square
            box_derivative_square.
          bounded_interval64_atan_range center_value
            center_lower_reciprocal center_upper_reciprocal =
              SOME center_result /\
          bounded_object_q_interval_encloses
            (bounded_interval64_object_q_cv center_value) object_center /\
          bounded_object_q_square_certificate_exact object_center
            (bounded_interval64_object_q_cv center_value)
            (bounded_interval64_object_q_cv center_square) /\
          bounded_object_q_square_certificate_exact object_value
            (bounded_interval64_object_q_cv value_bound)
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
          object_next =
            (bounded_object_q_taylor_atan radii weights
               (bounded_interval64_object_q_cv center_result)
               (bounded_interval64_object_q_cv center_derivative)
               (bounded_interval64_object_q_cv box_derivative)
               (bounded_interval64_object_q_cv box_derivative_square)
               (BoundedObjectQTaylor object_domain object_center
                 object_center_gradient object_value object_gradient_bounds
                 object_hessian)::rest,
             certificate_rest)
    | (BoundedAnalyticPiHalf,(stack,certificates)) =>
        object_next =
          (bounded_object_q_taylor_interval_constant bounded_atan_pi_half::
             stack,
           certificates)
    | _ => F
End

Theorem bounded_analytic64_polynomial_step_refines_object_q:
  LIST_REL (bounded_analytic_poly_instruction_refines 6)
      source_program prepared_program /\
  bounded_analytic64_state_covers_object_q
      (word_stack,certificates) (object_stack,certificates) /\
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      (BoundedAnalytic64Polynomial prepared_program)
      (word_stack,certificates) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      (BoundedAnalyticPolynomial source_program)
      (object_stack,certificates) object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_taylor64_program_eval radii center_environment box_environment
          prepared_program = SOME word_result`
  >> mp_tac
       (Q.INST
         [`source_program` |-> `source_program`,
          `prepared_program` |-> `prepared_program`,
          `center_environment` |-> `center_environment`,
          `object_center_environment` |-> `object_center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |-> `object_box_environment`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `word_result` |-> `word_result`]
         compute_boundedAnalyticObjectPolyRunRefinementTheory.bounded_taylor64_poly_eval_refines)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then (qx_choose_then `object_result` strip_assume_tac)
  >> qexists_tac `(object_result::object_stack,certificates)`
  >> simp [bounded_object_q_analytic_ordinary_step_def,
           bounded_analytic64_state_covers_object_q_def,
           compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
           LIST_REL_def]
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_neg_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_value::word_rest,certificates)
      (object_value::object_rest,certificates) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Neg (word_value::word_rest,certificates) =
        SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticNeg (object_value::object_rest,certificates)
      object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1 `bounded_taylor64_neg_complete radii word_value = SOME result`
  >> qexists_tac
       `(bounded_object_q_taylor_neg radii weights object_value::object_rest,
         certificates)`
  >> simp [bounded_object_q_analytic_ordinary_step_def,
           bounded_analytic64_state_covers_object_q_def,
           compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
           LIST_REL_def]
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> metis_tac
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_neg]
QED

Theorem bounded_analytic64_add_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_right::word_left::word_rest,certificates)
      (object_right::object_left::object_rest,certificates) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Add
      (word_right::word_left::word_rest,certificates) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticAdd
      (object_right::object_left::object_rest,certificates) object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_taylor64_add_complete radii word_left word_right = SOME result`
  >> qexists_tac
       `(bounded_object_q_taylor_add radii weights object_left object_right::
           object_rest,
         certificates)`
  >> simp [bounded_object_q_analytic_ordinary_step_def,
           bounded_analytic64_state_covers_object_q_def,
           compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
           LIST_REL_def]
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> metis_tac
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_add]
QED

Theorem bounded_analytic64_mul_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_right::word_left::word_rest,certificates)
      (object_right::object_left::object_rest,certificates) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Mul
      (word_right::word_left::word_rest,certificates) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticMul
      (object_right::object_left::object_rest,certificates) object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1 `bounded_taylor64_mul radii word_left word_right = SOME result`
  >> qexists_tac
       `(bounded_object_q_taylor_mul radii weights object_left object_right::
           object_rest,
         certificates)`
  >> simp [bounded_object_q_analytic_ordinary_step_def,
           bounded_analytic64_state_covers_object_q_def,
           compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
           LIST_REL_def]
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> metis_tac
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_mul]
QED

Theorem bounded_analytic64_square_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_value::word_rest,certificates)
      (object_value::object_rest,certificates) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Square (word_value::word_rest,certificates) =
        SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticSquare (object_value::object_rest,certificates)
      object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1 `bounded_taylor64_mul radii word_value word_value = SOME result`
  >> qexists_tac
       `(bounded_object_q_taylor_mul radii weights object_value object_value::
           object_rest,
         certificates)`
  >> simp [bounded_object_q_analytic_ordinary_step_def,
           bounded_analytic64_state_covers_object_q_def,
           compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
           LIST_REL_def]
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> metis_tac
       [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_mul]
QED

Theorem bounded_analytic64_pi_half_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_stack,certificates) (object_stack,certificates) /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64PiHalf (word_stack,certificates) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment
      BoundedAnalyticPiHalf (object_stack,certificates) object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> qexists_tac
       `(bounded_object_q_taylor_interval_constant bounded_atan_pi_half::
           object_stack,
         certificates)`
  >> simp [bounded_object_q_analytic_ordinary_step_def,
           bounded_analytic64_state_covers_object_q_def,
           compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
           LIST_REL_def]
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> metis_tac [bounded_taylor64_pi_half_refines_object_q_taylor]
QED

Theorem bounded_analytic64_sqrt_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_value::word_rest,
       BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::
         certificate_rest)
      (object_value::object_rest,
       BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::
         certificate_rest) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Sqrt
      (word_value::word_rest,
       BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::
         certificate_rest) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment BoundedAnalyticSqrt
      (object_value::object_rest,
       BoundedAnalytic64SqrtCertificate center_sqrt box_sqrt
         center_derivative box_derivative box_second_reciprocal::
         certificate_rest)
      object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `object_value`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_box object_gradient_bounds object_hessian`
  >> strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_taylor64_sqrt radii center_sqrt box_sqrt center_derivative
          box_derivative box_second_reciprocal word_value = SOME result`
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`source` |-> `word_value`,
          `object_source` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_box object_gradient_bounds
               object_hessian`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `center_sqrt` |-> `center_sqrt`, `box_sqrt` |-> `box_sqrt`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`,
          `box_second_reciprocal` |-> `box_second_reciprocal`,
          `result` |-> `result`]
         bounded_taylor64_sqrt_refines_object_q_taylor)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then strip_assume_tac
  >> qexists_tac
       `(bounded_object_q_taylor_sqrt radii weights
           (bounded_interval64_object_q_cv center_sqrt)
           (bounded_interval64_object_q_cv center_derivative)
           (bounded_interval64_object_q_cv box_derivative)
           (bounded_interval64_object_q_cv box_second_reciprocal)
           (BoundedObjectQTaylor object_domain object_center
             object_center_gradient object_box object_gradient_bounds
             object_hessian)::object_rest,
         certificate_rest)`
  >> gvs [bounded_object_q_analytic_ordinary_step_def,
          bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_inverse_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_value::word_rest,
       BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
         certificate_rest)
      (object_value::object_rest,
       BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
         certificate_rest) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Inverse
      (word_value::word_rest,
       BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
         certificate_rest) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment BoundedAnalyticInverse
      (object_value::object_rest,
       BoundedAnalytic64InverseCertificate center_reciprocal box_reciprocal::
         certificate_rest)
      object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `object_value`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_box object_gradient_bounds object_hessian`
  >> strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_taylor64_inverse radii center_reciprocal box_reciprocal
          word_value = SOME result`
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`source` |-> `word_value`,
          `object_source` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_box object_gradient_bounds
               object_hessian`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `center_reciprocal` |-> `center_reciprocal`,
          `box_reciprocal` |-> `box_reciprocal`, `result` |-> `result`]
         bounded_taylor64_inverse_refines_object_q_taylor)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then strip_assume_tac
  >> qexists_tac
       `(bounded_object_q_taylor_inverse radii weights
           (bounded_interval64_object_q_cv center_reciprocal)
           (bounded_interval64_object_q_cv box_reciprocal)
           (BoundedObjectQTaylor object_domain object_center
             object_center_gradient object_box object_gradient_bounds
             object_hessian)::object_rest,
         certificate_rest)`
  >> gvs [bounded_object_q_analytic_ordinary_step_def,
          bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
QED

Theorem bounded_analytic64_atan_step_refines_object_q:
  bounded_analytic64_state_covers_object_q
      (word_value::word_rest,
       BoundedAnalytic64AtanCertificate center_lower_reciprocal
         center_upper_reciprocal center_derivative box_derivative::
         certificate_rest)
      (object_value::object_rest,
       BoundedAnalytic64AtanCertificate center_lower_reciprocal
         center_upper_reciprocal center_derivative box_derivative::
         certificate_rest) /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_analytic64_program_step radii center_environment box_environment
      BoundedAnalytic64Atan
      (word_value::word_rest,
       BoundedAnalytic64AtanCertificate center_lower_reciprocal
         center_upper_reciprocal center_derivative box_derivative::
         certificate_rest) = SOME word_next ==>
  ?object_next.
    bounded_object_q_analytic_ordinary_step radii weights
      object_center_environment object_box_environment BoundedAnalyticAtan
      (object_value::object_rest,
       BoundedAnalytic64AtanCertificate center_lower_reciprocal
         center_upper_reciprocal center_derivative box_derivative::
         certificate_rest)
      object_next /\
    bounded_analytic64_state_covers_object_q word_next object_next
Proof
  Cases_on `object_value`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_box object_gradient_bounds object_hessian`
  >> strip_tac
  >> fs [compute_boundedAnalyticProgramTheory.bounded_analytic64_program_step_def]
  >> every_case_tac
  >> gvs []
  >> rename1
       `bounded_taylor64_atan radii center_lower_reciprocal
          center_upper_reciprocal center_derivative box_derivative
          word_value = SOME result`
  >> gvs [bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> mp_tac
       (Q.INST
         [`source` |-> `word_value`,
          `object_source` |->
            `BoundedObjectQTaylor object_domain object_center
               object_center_gradient object_box object_gradient_bounds
               object_hessian`,
          `radii` |-> `radii`, `weights` |-> `weights`,
          `center_lower_reciprocal` |-> `center_lower_reciprocal`,
          `center_upper_reciprocal` |-> `center_upper_reciprocal`,
          `center_derivative` |-> `center_derivative`,
          `box_derivative` |-> `box_derivative`, `result` |-> `result`]
         bounded_taylor64_atan_refines_object_q_taylor)
  >> impl_tac >- asm_rewrite_tac []
  >> disch_then
       (qx_choose_then `center_value`
         (qx_choose_then `value_bound`
           (qx_choose_then `center_result`
             (qx_choose_then `center_square`
               (qx_choose_then `box_square`
                 (qx_choose_then `box_derivative_square`
                   strip_assume_tac))))))
  >> qexists_tac
       `(bounded_object_q_taylor_atan radii weights
           (bounded_interval64_object_q_cv center_result)
           (bounded_interval64_object_q_cv center_derivative)
           (bounded_interval64_object_q_cv box_derivative)
           (bounded_interval64_object_q_cv box_derivative_square)
           (BoundedObjectQTaylor object_domain object_center
             object_center_gradient object_box object_gradient_bounds
             object_hessian)::object_rest,
         certificate_rest)`
  >> gvs [bounded_object_q_analytic_ordinary_step_def,
          bounded_analytic64_state_covers_object_q_def,
          compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_stack_covers_object_q_def,
          LIST_REL_def]
  >> metis_tac []
QED

val _ = export_theory ();
