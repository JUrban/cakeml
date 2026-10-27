(*****************************************************************************
 * Object-q semantics for the ordinary outer analytic instructions.
 *
 * The operation refinement theories expose complete six-field Taylor states,
 * but their conclusions are intentionally written field by field.  This
 * theory packages those conclusions as object-state constructors before the
 * enclosing stack/program proof.  Certificate validity remains explicit and
 * the recognized delta instructions are deliberately not included here.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectProgramSemantics
Ancestors
  compute_boundedAnalyticObjectPolyRunRefinement
Libs
  bossLib preamble

Definition bounded_object_q_taylor_unary_def:
  bounded_object_q_taylor_unary radii weights result_domain center_result
      center_derivative box_derivative box_second
      (BoundedObjectQTaylor source_domain source_center
        source_center_gradient source_value source_gradient_bounds
        source_hessian) =
    let result_center_gradient =
          bounded_object_q_interval_list_scale_cv center_derivative
            source_center_gradient;
        result_hessian =
          bounded_object_q_taylor_unary_hessian_cv box_derivative box_second
            source_gradient_bounds source_hessian
    in
      BoundedObjectQTaylor (source_domain /\ result_domain) center_result
        result_center_gradient
        (bounded_object_q_taylor_value_complete_cv center_result
          (bounded_object_q_taylor_error_cv radii result_center_gradient
            weights result_hessian))
        (bounded_object_q_taylor_gradient_complete_cv radii
          result_center_gradient result_hessian)
        result_hessian
End

Definition bounded_object_q_taylor_sqrt_def:
  bounded_object_q_taylor_sqrt radii weights center_sqrt center_derivative
      box_derivative box_second_reciprocal source =
    bounded_object_q_taylor_unary radii weights T center_sqrt
      center_derivative box_derivative
      (bounded_object_q_interval_neg_cv box_second_reciprocal) source
End

Definition bounded_object_q_taylor_inverse_def:
  bounded_object_q_taylor_inverse radii weights center_reciprocal
      box_reciprocal source =
    bounded_object_q_taylor_unary radii weights T center_reciprocal
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv center_reciprocal
          center_reciprocal))
      (bounded_object_q_interval_neg_cv
        (bounded_object_q_interval_mul_cv box_reciprocal box_reciprocal))
      (bounded_object_q_interval_add_cv
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_mul_cv box_reciprocal box_reciprocal)
          box_reciprocal)
        (bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_mul_cv box_reciprocal box_reciprocal)
          box_reciprocal))
      source
End

Definition bounded_object_q_taylor_atan_def:
  bounded_object_q_taylor_atan radii weights center_result center_derivative
      box_derivative box_derivative_square
      (BoundedObjectQTaylor source_domain source_center
        source_center_gradient source_value source_gradient_bounds
        source_hessian) =
    bounded_object_q_taylor_unary radii weights T center_result
      center_derivative box_derivative
      (bounded_object_q_atan_second_cv source_value box_derivative_square)
      (BoundedObjectQTaylor source_domain source_center
        source_center_gradient source_value source_gradient_bounds
        source_hessian)
End

Definition bounded_object_q_taylor_interval_constant_def:
  bounded_object_q_taylor_interval_constant interval =
    BoundedObjectQTaylor T (bounded_interval64_object_q_cv interval)
      (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0))
      (bounded_interval64_object_q_cv interval)
      (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0))
      (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0))
End

Theorem bounded_taylor64_sqrt_refines_object_q_taylor:
  bounded_taylor64_covers_object_q source object_source /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_sqrt radii center_sqrt box_sqrt center_derivative
    box_derivative box_second_reciprocal source = SOME result ==>
  bounded_object_q_sqrt_certificate_exact
    (case object_source of BoundedObjectQTaylor _ center _ _ _ _ => center)
    (bounded_interval64_object_q_cv center_sqrt) /\
  bounded_object_q_sqrt_certificate_exact
    (case object_source of BoundedObjectQTaylor _ _ _ value _ _ => value)
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
        (case object_source of
         | BoundedObjectQTaylor _ _ _ value _ _ => value)
        (case object_source of
         | BoundedObjectQTaylor _ _ _ value _ _ => value)))
    (bounded_interval64_object_q_cv box_second_reciprocal) /\
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_sqrt radii weights
      (bounded_interval64_object_q_cv center_sqrt)
      (bounded_interval64_object_q_cv center_derivative)
      (bounded_interval64_object_q_cv box_derivative)
      (bounded_interval64_object_q_cv box_second_reciprocal) object_source)
Proof
  Cases_on `object_source`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_value object_gradient_bounds object_hessian`
  >> strip_tac
  >> fs [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectSqrtOperationRefinementTheory.bounded_taylor64_sqrt_covers_object_q_state
  >> gvs []
  >> fs [bounded_object_q_taylor_sqrt_def,
         bounded_object_q_taylor_unary_def,
         compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
QED

Theorem bounded_taylor64_inverse_refines_object_q_taylor:
  bounded_taylor64_covers_object_q source object_source /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_inverse radii center_reciprocal box_reciprocal source =
    SOME result ==>
  bounded_object_q_inv_certificate_exact
    (case object_source of BoundedObjectQTaylor _ center _ _ _ _ => center)
    (bounded_interval64_object_q_cv center_reciprocal) /\
  bounded_object_q_inv_certificate_exact
    (case object_source of BoundedObjectQTaylor _ _ _ value _ _ => value)
    (bounded_interval64_object_q_cv box_reciprocal) /\
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_inverse radii weights
      (bounded_interval64_object_q_cv center_reciprocal)
      (bounded_interval64_object_q_cv box_reciprocal) object_source)
Proof
  Cases_on `object_source`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_value object_gradient_bounds object_hessian`
  >> strip_tac
  >> fs [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectInverseOperationRefinementTheory.bounded_taylor64_inverse_covers_object_q_state
  >> gvs []
  >> fs [bounded_object_q_taylor_inverse_def,
         bounded_object_q_taylor_unary_def,
         compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
QED

Theorem bounded_taylor64_atan_refines_object_q_taylor:
  bounded_taylor64_covers_object_q source object_source /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_atan radii center_lower_reciprocal
    center_upper_reciprocal center_derivative box_derivative source =
    SOME result ==>
  ?center_value center_result box_derivative_square.
    bounded_interval64_atan_range center_value center_lower_reciprocal
      center_upper_reciprocal = SOME center_result /\
    bounded_object_q_interval_encloses
      (bounded_interval64_object_q_cv center_value)
      (case object_source of
       | BoundedObjectQTaylor _ center _ _ _ _ => center) /\
    bounded_taylor64_covers_object_q result
      (bounded_object_q_taylor_atan radii weights
        (bounded_interval64_object_q_cv center_result)
        (bounded_interval64_object_q_cv center_derivative)
        (bounded_interval64_object_q_cv box_derivative)
        (bounded_interval64_object_q_cv box_derivative_square) object_source)
Proof
  Cases_on `object_source`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center object_center_gradient
          object_value object_gradient_bounds object_hessian`
  >> strip_tac
  >> fs [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
  >> imp_res_tac
       compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_taylor64_atan_covers_object_q_state
  >> gvs []
  >> qexistsl_tac [`center_value`, `center_result`, `box_derivative_square`]
  >> asm_rewrite_tac []
  >> fs [bounded_object_q_taylor_atan_def,
         bounded_object_q_taylor_unary_def,
         compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def]
QED

Theorem bounded_atan_pi_half_valid:
  bounded_interval64_valid bounded_atan_pi_half
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

Theorem bounded_taylor64_pi_half_refines_object_q_taylor:
  bounded_taylor64_constant bounded_atan_pi_half = SOME result ==>
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_interval_constant bounded_atan_pi_half)
Proof
  strip_tac
  >> fs [compute_boundedTaylorBaseTheory.bounded_taylor64_constant_def,
         compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
         compute_boundedTaylorStateTheory.bounded_taylor64_well_formed_def,
         compute_boundedTaylorBaseTheory.bounded_interval64_zeros_def]
  >> gvs [compute_boundedAnalyticObjectPolyProgramRefinementTheory.bounded_taylor64_covers_object_q_def,
          bounded_object_q_taylor_interval_constant_def,
          compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_covers_object_q_state_def]
  >> simp
       [compute_boundedAnalyticObjectRefinementTheory.bounded_interval64_zeros_cover_object_q_zeros,
        compute_boundedAnalyticObjectCertificateRefinementTheory.bounded_interval64_covers_own_object_q,
        bounded_atan_pi_half_valid]
QED

val _ = export_theory ();
