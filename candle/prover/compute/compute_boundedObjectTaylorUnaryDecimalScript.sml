(*****************************************************************************
 * Exact object trace for decimal unary Taylor completion.
 *
 * The theorem in this file exposes every object-level operation corresponding
 * to a successful compact unary chain-rule calculation.  It is phrased as a
 * trace so later square-root, reciprocal, arctangent, and dihedral refinements
 * can rewrite the authenticated object program without re-evaluating its
 * numerical arithmetic.
 *****************************************************************************)
Theory compute_boundedObjectTaylorUnaryDecimal
Ancestors
  compute_boundedObjectTaylorStateDecimal
Libs
  bossLib preamble

Definition bounded_object_cv_list_append_def:
  bounded_object_cv_list_append (Num 0) right = SOME right /\
  bounded_object_cv_list_append (Num (SUC value)) right = NONE /\
  bounded_object_cv_list_append (Pair entry rest) right =
    case bounded_object_cv_list_append rest right of
    | NONE => NONE
    | SOME result => SOME (Pair entry result)
End

Definition bounded_object_fs_interval_self_outer_decimal_def:
  bounded_object_fs_interval_self_outer_decimal [] = SOME (Num 0 : cv) /\
  bounded_object_fs_interval_self_outer_decimal (entry::rest) =
    case bounded_object_fs_interval_list_scale_decimal entry (entry::rest) of
    | NONE => NONE
    | SOME row =>
      case bounded_object_fs_interval_self_outer_decimal rest of
      | NONE => NONE
      | SOME rows =>
          case bounded_object_cv_list_append row rows of
          | NONE => NONE
          | SOME result => SOME result
End

Theorem bounded_object_cv_list_append_interval_lists:
  bounded_object_cv_list_append
      (bounded_interval64_object_cv_list left)
      (bounded_interval64_object_cv_list right) =
    SOME (bounded_interval64_object_cv_list (left ++ right))
Proof
  Induct_on `left`
  >> simp
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        bounded_object_cv_list_append_def]
QED

Theorem bounded_object_fs_interval_self_outer_decimal_exact:
  !result.
    bounded_interval64_self_outer_decimal values = SOME result ==>
    bounded_object_fs_interval_self_outer_decimal values =
      SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `values`
  >> rw
       [compute_boundedTaylorUnaryDecimalTheory.bounded_interval64_self_outer_decimal_def,
        bounded_object_fs_interval_self_outer_decimal_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> res_tac
  >> gvs [bounded_object_cv_list_append_interval_lists]
QED

Theorem bounded_taylor64_unary_complete_decimal_object_trace:
  bounded_taylor64_unary_complete_decimal radii result_domain center_result
      center_derivative box_derivative box_second source = SOME result ==>
  ?source_domain source_center source_center_gradient source_value
   source_gradient_bounds source_hessian center_gradient gradient_outer
   outer_hessian source_hessian_scaled hessian.
    source =
      BoundedTaylor64 source_domain source_center source_center_gradient
        source_value source_gradient_bounds source_hessian /\
    bounded_interval64_list_scale_decimal center_derivative
      source_center_gradient = SOME center_gradient /\
    bounded_interval64_self_outer_decimal source_gradient_bounds =
      SOME gradient_outer /\
    bounded_interval64_list_scale_decimal box_second gradient_outer =
      SOME outer_hessian /\
    bounded_interval64_list_scale_decimal box_derivative source_hessian =
      SOME source_hessian_scaled /\
    bounded_interval64_list_add outer_hessian source_hessian_scaled =
      SOME hessian /\
    bounded_object_fs_interval_list_scale_decimal center_derivative
      source_center_gradient =
      SOME (bounded_interval64_object_cv_list center_gradient) /\
    bounded_object_fs_interval_self_outer_decimal source_gradient_bounds =
      SOME (bounded_interval64_object_cv_list gradient_outer) /\
    bounded_object_fs_interval_list_scale_decimal box_second gradient_outer =
      SOME (bounded_interval64_object_cv_list outer_hessian) /\
    bounded_object_fs_interval_list_scale_decimal box_derivative
      source_hessian =
      SOME (bounded_interval64_object_cv_list source_hessian_scaled) /\
    bounded_object_fs_interval_list_add outer_hessian
      source_hessian_scaled =
      SOME (bounded_interval64_object_cv_list hessian) /\
    (!hessian_rows.
       bounded_hessian64_rows hessian = SOME hessian_rows ==>
       bounded_object_fs_taylor_complete radii
         (source_domain /\ result_domain) center_result center_gradient
         hessian hessian_rows =
       SOME (bounded_taylor64_rows_object_cv result hessian_rows))
Proof
  Cases_on `source`
  >> rw
       [compute_boundedTaylorUnaryDecimalTheory.bounded_taylor64_unary_complete_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> imp_res_tac bounded_object_fs_interval_self_outer_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_fs_interval_list_add_exact
  >> rpt (first_assum (irule_at Any))
  >> rw []
  >> metis_tac
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact]
QED

val _ = export_theory ();
