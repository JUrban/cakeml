(*****************************************************************************
 * Object-q semantics and refinement for generic polynomial postfix blocks.
 *
 * The executable stack contains compact scale-2^40 Taylor states.  The proof
 * stack below packages the exact rational fields already used by the
 * operation refinements.  Keeping the stack relation explicit makes operand
 * order, underflow, and completion boundaries visible before the enclosing
 * nonlinear program and certificate stream are considered.
 *****************************************************************************)
Theory compute_boundedAnalyticObjectPolyProgramRefinement
Ancestors
  compute_boundedAnalyticObjectProgramOperationRefinement
Libs
  bossLib preamble

Datatype:
  bounded_object_q_taylor_state =
    BoundedObjectQTaylor bool cv (cv list) cv (cv list) (cv list)
End

Definition bounded_taylor64_covers_object_q_def:
  bounded_taylor64_covers_object_q word_state
      (BoundedObjectQTaylor object_domain object_center_value
        object_center_gradient object_value_bound object_gradient_bounds
        object_hessian) <=>
    bounded_taylor64_covers_object_q_state word_state object_domain
      object_center_value object_center_gradient object_value_bound
      object_gradient_bounds object_hessian
End

Definition bounded_taylor64_stack_covers_object_q_def:
  bounded_taylor64_stack_covers_object_q word_stack object_stack <=>
    LIST_REL bounded_taylor64_covers_object_q word_stack object_stack
End

Definition bounded_object_q_taylor_constant_def:
  bounded_object_q_taylor_constant positive negative denominator_predecessor =
    BoundedObjectQTaylor T
      (bounded_analytic_source_q_interval_cv positive negative
        denominator_predecessor)
      (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0))
      (bounded_analytic_source_q_interval_cv positive negative
        denominator_predecessor)
      (REPLICATE 6 (bounded_analytic_source_q_interval_cv 0 0 0))
      (REPLICATE 21 (bounded_analytic_source_q_interval_cv 0 0 0))
End

Definition bounded_object_q_taylor_variable_def:
  bounded_object_q_taylor_variable center_environment box_environment index =
    case bounded_object_q_nth center_environment index of
    | NONE => NONE
    | SOME center =>
      case bounded_object_q_nth box_environment index of
      | NONE => NONE
      | SOME value =>
          SOME
            (BoundedObjectQTaylor T center
              (bounded_object_q_unit_vector index) value
              (bounded_object_q_unit_vector index)
              (REPLICATE 21
                (bounded_analytic_source_q_interval_cv 0 0 0)))
End

Definition bounded_object_q_taylor_neg_def:
  bounded_object_q_taylor_neg radii weights
      (BoundedObjectQTaylor domain center center_gradient value_bound
        gradient_bounds hessian) =
    let result_center = bounded_object_q_interval_neg_cv center;
        result_center_gradient =
          MAP bounded_object_q_interval_neg_cv center_gradient;
        result_hessian = MAP bounded_object_q_interval_neg_cv hessian
    in
      BoundedObjectQTaylor domain result_center result_center_gradient
        (bounded_object_q_taylor_value_complete_cv result_center
          (bounded_object_q_taylor_error_cv radii result_center_gradient
            weights result_hessian))
        (bounded_object_q_taylor_gradient_complete_cv radii
          result_center_gradient result_hessian)
        result_hessian
End

Definition bounded_object_q_taylor_add_def:
  bounded_object_q_taylor_add radii weights
      (BoundedObjectQTaylor left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedObjectQTaylor right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    let result_center =
          bounded_object_q_interval_add_cv left_center right_center;
        result_center_gradient =
          MAP2 bounded_object_q_interval_add_cv
            left_center_gradient right_center_gradient;
        result_hessian =
          MAP2 bounded_object_q_interval_add_cv
            left_hessian right_hessian
    in
      BoundedObjectQTaylor (left_domain /\ right_domain)
        result_center result_center_gradient
        (bounded_object_q_taylor_value_complete_cv result_center
          (bounded_object_q_taylor_error_cv radii result_center_gradient
            weights result_hessian))
        (bounded_object_q_taylor_gradient_complete_cv radii
          result_center_gradient result_hessian)
        result_hessian
End

Definition bounded_object_q_taylor_mul_def:
  bounded_object_q_taylor_mul radii weights
      (BoundedObjectQTaylor left_domain left_center left_center_gradient
        left_value left_gradient_bounds left_hessian)
      (BoundedObjectQTaylor right_domain right_center right_center_gradient
        right_value right_gradient_bounds right_hessian) =
    let result_center = bounded_object_q_interval_mul_cv left_center right_center;
        result_center_gradient =
          bounded_object_q_interval_fused_scale_add_cv
            right_center left_center_gradient
            left_center right_center_gradient;
        result_hessian =
          bounded_object_q_interval_fused_hessian_cv
            left_value right_value left_hessian right_hessian
            (bounded_object_q_symmetric_product_pairs_cv
              left_gradient_bounds right_gradient_bounds)
    in
      BoundedObjectQTaylor (left_domain /\ right_domain)
        result_center result_center_gradient
        (bounded_object_q_taylor_value_complete_cv result_center
          (bounded_object_q_taylor_error_cv radii result_center_gradient
            weights result_hessian))
        (bounded_object_q_taylor_gradient_complete_cv radii
          result_center_gradient result_hessian)
        result_hessian
End

Definition bounded_object_q_poly_step_def:
  bounded_object_q_poly_step radii weights center_environment box_environment
      instruction stack =
    case instruction of
    | BoundedPolyConstant positive negative denominator_predecessor =>
        SOME
          (bounded_object_q_taylor_constant positive negative
            denominator_predecessor::stack)
    | BoundedPolyVariable index =>
        (case bounded_object_q_taylor_variable center_environment
          box_environment index of
         | NONE => NONE
         | SOME result => SOME (result::stack))
    | BoundedPolyNeg =>
        (case stack of
         | value::rest =>
             SOME (bounded_object_q_taylor_neg radii weights value::rest)
         | _ => NONE)
    | BoundedPolyAdd =>
        (case stack of
         | right::left::rest =>
             SOME
               (bounded_object_q_taylor_add radii weights left right::rest)
         | _ => NONE)
    | BoundedPolyMul =>
        (case stack of
         | right::left::rest =>
             SOME
               (bounded_object_q_taylor_mul radii weights left right::rest)
         | _ => NONE)
    | BoundedPolySquare =>
        (case stack of
         | value::rest =>
             SOME
               (bounded_object_q_taylor_mul radii weights value value::rest)
         | _ => NONE)
End

Theorem bounded_taylor64_covers_object_q_constant:
  bounded_analytic_rational_constant64 positive negative
      denominator_predecessor = SOME word_interval /\
  bounded_taylor64_constant word_interval = SOME result ==>
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_constant positive negative
      denominator_predecessor)
Proof
  rw [bounded_taylor64_covers_object_q_def,
      bounded_object_q_taylor_constant_def]
  >> metis_tac
       [compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_constant_covers_source_q]
QED

Theorem bounded_taylor64_covers_object_q_variable:
  LIST_REL bounded_interval64_covers_object_q
      center_environment object_center_environment /\
  LIST_REL bounded_interval64_covers_object_q
      box_environment object_box_environment /\
  bounded_taylor64_variable center_environment box_environment index =
      SOME result ==>
  ?object_result.
    bounded_object_q_taylor_variable object_center_environment
      object_box_environment index = SOME object_result /\
    bounded_taylor64_covers_object_q result object_result
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`center_environment` |-> `center_environment`,
          `object_center_environment` |-> `object_center_environment`,
          `box_environment` |-> `box_environment`,
          `object_box_environment` |-> `object_box_environment`,
          `index` |-> `index`, `result` |-> `result`]
         compute_boundedAnalyticObjectRefinementTheory.bounded_taylor64_variable_covers_object_q)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> qexists_tac
       `BoundedObjectQTaylor T object_center
          (bounded_object_q_unit_vector index) object_box
          (bounded_object_q_unit_vector index)
          (REPLICATE 21
            (bounded_analytic_source_q_interval_cv 0 0 0))`
  >> simp [bounded_object_q_taylor_variable_def,
           bounded_taylor64_covers_object_q_def]
QED

Theorem bounded_taylor64_covers_object_q_neg:
  bounded_taylor64_covers_object_q source object_source /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_neg_complete radii source = SOME result ==>
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_neg radii weights object_source)
Proof
  Cases_on `object_source`
  >> rename1
       `BoundedObjectQTaylor object_domain object_center
          object_center_gradient object_value object_gradient_bounds
          object_hessian`
  >> rw [bounded_taylor64_covers_object_q_def,
         bounded_object_q_taylor_neg_def]
  >> mp_tac
       (Q.INST
         [`source` |-> `source`, `object_domain` |-> `object_domain`,
          `object_center_value` |-> `object_center`,
          `object_center_gradient` |-> `object_center_gradient`,
          `object_value_bound` |-> `object_value`,
          `object_gradient_bounds` |-> `object_gradient_bounds`,
          `object_hessian` |-> `object_hessian`,
          `radii` |-> `radii`, `result` |-> `result`]
         bounded_taylor64_neg_complete_covers_object_q_state)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> gvs []
QED

Theorem bounded_taylor64_covers_object_q_add:
  bounded_taylor64_covers_object_q left object_left /\
  bounded_taylor64_covers_object_q right object_right /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_add_complete radii left right = SOME result ==>
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_add radii weights object_left object_right)
Proof
  Cases_on `object_left`
  >> rename1
       `bounded_taylor64_covers_object_q left
          (BoundedObjectQTaylor left_object_domain left_object_center
            left_object_center_gradient left_object_value
            left_object_gradient_bounds left_object_hessian) /\ _`
  >> Cases_on `object_right`
  >> rename1
       `bounded_taylor64_covers_object_q right
          (BoundedObjectQTaylor right_object_domain right_object_center
            right_object_center_gradient right_object_value
            right_object_gradient_bounds right_object_hessian)`
  >> rw [bounded_taylor64_covers_object_q_def,
         bounded_object_q_taylor_add_def]
  >> mp_tac
       (Q.INST
         [`left` |-> `left`, `right` |-> `right`,
          `left_object_domain` |-> `left_object_domain`,
          `left_object_center_value` |-> `left_object_center`,
          `left_object_center_gradient` |-> `left_object_center_gradient`,
          `left_object_value_bound` |-> `left_object_value`,
          `left_object_gradient_bounds` |-> `left_object_gradient_bounds`,
          `left_object_hessian` |-> `left_object_hessian`,
          `right_object_domain` |-> `right_object_domain`,
          `right_object_center_value` |-> `right_object_center`,
          `right_object_center_gradient` |-> `right_object_center_gradient`,
          `right_object_value_bound` |-> `right_object_value`,
          `right_object_gradient_bounds` |-> `right_object_gradient_bounds`,
          `right_object_hessian` |-> `right_object_hessian`,
          `radii` |-> `radii`, `result` |-> `result`]
         bounded_taylor64_add_complete_covers_object_q_state)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> gvs []
QED

Theorem bounded_taylor64_covers_object_q_mul:
  bounded_taylor64_covers_object_q left object_left /\
  bounded_taylor64_covers_object_q right object_right /\
  bounded_taylor_radius_pairs radii = SOME weights /\
  bounded_taylor64_mul radii left right = SOME result ==>
  bounded_taylor64_covers_object_q result
    (bounded_object_q_taylor_mul radii weights object_left object_right)
Proof
  Cases_on `object_left`
  >> rename1
       `bounded_taylor64_covers_object_q left
          (BoundedObjectQTaylor left_object_domain left_object_center
            left_object_center_gradient left_object_value
            left_object_gradient_bounds left_object_hessian) /\ _`
  >> Cases_on `object_right`
  >> rename1
       `bounded_taylor64_covers_object_q right
          (BoundedObjectQTaylor right_object_domain right_object_center
            right_object_center_gradient right_object_value
            right_object_gradient_bounds right_object_hessian)`
  >> rw [bounded_taylor64_covers_object_q_def,
         bounded_object_q_taylor_mul_def]
  >> mp_tac
       (Q.INST
         [`left` |-> `left`, `right` |-> `right`,
          `left_object_domain` |-> `left_object_domain`,
          `left_object_center_value` |-> `left_object_center`,
          `left_object_center_gradient` |-> `left_object_center_gradient`,
          `left_object_value_bound` |-> `left_object_value`,
          `left_object_gradient_bounds` |-> `left_object_gradient_bounds`,
          `left_object_hessian` |-> `left_object_hessian`,
          `right_object_domain` |-> `right_object_domain`,
          `right_object_center_value` |-> `right_object_center`,
          `right_object_center_gradient` |-> `right_object_center_gradient`,
          `right_object_value_bound` |-> `right_object_value`,
          `right_object_gradient_bounds` |-> `right_object_gradient_bounds`,
          `right_object_hessian` |-> `right_object_hessian`,
          `radii` |-> `radii`, `result` |-> `result`]
         bounded_taylor64_mul_covers_object_q_state)
  >> impl_tac >- asm_rewrite_tac []
  >> strip_tac
  >> gvs []
QED

val _ = export_theory ();
