(*****************************************************************************
 * Exact list-level refinement for decimal Taylor product operations.
 *
 * These object helpers use the same cv constructors and raw/final-rounding
 * operations as the authenticated checker source.  The theorems lift the
 * scalar and fused interval bridges to the gradient and Hessian list shapes
 * used by the specialized case-10173 checker.
 *****************************************************************************)
Theory compute_boundedObjectTaylorProductDecimal
Ancestors
  compute_boundedObjectDecimalDecode compute_boundedObjectDecimalFused
  compute_boundedTaylorProductDecimal
Libs
  bossLib preamble

Definition bounded_object_fs_interval_list_scale_decimal_def:
  bounded_object_fs_interval_list_scale_decimal scalar [] =
    SOME (Num 0 : cv) /\
  bounded_object_fs_interval_list_scale_decimal scalar (value::rest) =
    case bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv scalar)
      (bounded_interval64_object_cv value) of
    | NONE => NONE
    | SOME product =>
      case bounded_object_fs_interval_list_scale_decimal scalar rest of
      | NONE => NONE
      | SOME products => SOME (Pair product products)
End

Theorem bounded_object_fs_interval_list_scale_decimal_exact:
  !values result.
    bounded_interval64_list_scale_decimal scalar values = SOME result ==>
    bounded_object_fs_interval_list_scale_decimal scalar values =
      SOME (bounded_interval64_object_cv_list result)
Proof
  Induct
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def,
        bounded_object_fs_interval_list_scale_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_fused_scale_add_decimal_def:
  bounded_object_fs_fused_scale_add_decimal
      left_scale [] right_scale [] = SOME (Num 0 : cv) /\
  bounded_object_fs_fused_scale_add_decimal left_scale (left::left_rest)
      right_scale (right::right_rest) =
    (case bounded_object_fs_fused_products_decimal
      [(left_scale,left);(right_scale,right)] of
    | NONE => NONE
    | SOME entry =>
      case bounded_object_fs_fused_scale_add_decimal left_scale left_rest
        right_scale right_rest of
      | NONE => NONE
      | SOME entries => SOME (Pair entry entries)) /\
  bounded_object_fs_fused_scale_add_decimal left_scale _ right_scale _ = NONE
End

Theorem bounded_object_fs_fused_scale_add_decimal_exact:
  !left right result.
    bounded_interval64_fused_scale_add_decimal
      left_scale left right_scale right = SOME result ==>
    bounded_object_fs_fused_scale_add_decimal
      left_scale left right_scale right =
        SOME (bounded_interval64_object_cv_list result)
Proof
  Induct
  >> Cases_on `right`
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_scale_add_decimal_def,
        bounded_object_fs_fused_scale_add_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> imp_res_tac bounded_object_fs_fused_products_decimal_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_fused_hessian_decimal_def:
  bounded_object_fs_fused_hessian_decimal
      left_value right_value [] [] [] = SOME (Num 0 : cv) /\
  bounded_object_fs_fused_hessian_decimal left_value right_value
      (left_hessian::left_rest) (right_hessian::right_rest)
      (outer::outer_rest) =
    (case bounded_object_fs_fused_products_decimal
      [(right_value,left_hessian);FST outer;SND outer;
       (left_value,right_hessian)] of
    | NONE => NONE
    | SOME entry =>
      case bounded_object_fs_fused_hessian_decimal left_value right_value
        left_rest right_rest outer_rest of
      | NONE => NONE
      | SOME entries => SOME (Pair entry entries)) /\
  bounded_object_fs_fused_hessian_decimal left_value right_value _ _ _ = NONE
End

Theorem bounded_object_fs_fused_hessian_decimal_exact:
  !left right outer result.
    bounded_interval64_fused_hessian_decimal
      left_value right_value left right outer = SOME result ==>
    bounded_object_fs_fused_hessian_decimal
      left_value right_value left right outer =
        SOME (bounded_interval64_object_cv_list result)
Proof
  Induct
  >> Cases_on `right`
  >> Cases_on `outer`
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_fused_hessian_decimal_def,
        bounded_object_fs_fused_hessian_decimal_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> imp_res_tac bounded_object_fs_fused_products_decimal_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

val _ = export_theory ();
