(*****************************************************************************
 * Exact object refinement for the compact decimal Taylor-state assembly.
 *
 * The specialized checker postpones Taylor completion while it adds the six
 * coordinate-square-root terms and the historical dihedral term.  This file
 * connects those compact, 21-Hessian-entry operations to the canonical cv
 * representation used by the authenticated object checker.  Matrix expansion
 * is deliberately left to the completion boundary, where it is already
 * checked by [bounded_hessian64_rows].
 *****************************************************************************)
Theory compute_boundedObjectTaylorStateDecimal
Ancestors
  compute_boundedObjectTaylorCompleteDecimal
  compute_boundedCase10173HistoricalCellDecimal
Libs
  bossLib preamble

Definition bounded_taylor64_flat_object_cv_def:
  bounded_taylor64_flat_object_cv
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    Pair (bounded_bool_object_cv domain)
      (Pair
        (Pair (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv_list center_gradient))
        (Pair (bounded_interval64_object_cv value_bound)
          (Pair (bounded_interval64_object_cv_list gradient_bounds)
            (bounded_interval64_object_cv_list hessian))))
End

Definition bounded_object_fs_interval_list_add_def:
  bounded_object_fs_interval_list_add [] [] = SOME (Num 0 : cv) /\
  bounded_object_fs_interval_list_add [] (_::_) = NONE /\
  bounded_object_fs_interval_list_add (_::_) [] = NONE /\
  bounded_object_fs_interval_list_add (left::left_rest)
      (right::right_rest) =
    case bounded_object_fs_interval_add
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) of
    | NONE => NONE
    | SOME value =>
      case bounded_object_fs_interval_list_add left_rest right_rest of
      | NONE => NONE
      | SOME rest => SOME (Pair value rest)
End

Theorem bounded_object_fs_interval_list_add_exact:
  !right result.
    bounded_interval64_list_add left right = SOME result ==>
    bounded_object_fs_interval_list_add left right =
      SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw
       [compute_boundedIntervalListTheory.bounded_interval64_list_add_def,
        bounded_object_fs_interval_list_add_def]
  >> every_case_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_interval64_matrix_scale_decimal_def:
  bounded_interval64_matrix_scale_decimal scalar [] = SOME [] /\
  bounded_interval64_matrix_scale_decimal scalar (row::rows) =
    case bounded_interval64_list_scale_decimal scalar row of
    | NONE => NONE
    | SOME scaled_row =>
      case bounded_interval64_matrix_scale_decimal scalar rows of
      | NONE => NONE
      | SOME scaled_rows => SOME (scaled_row::scaled_rows)
End

Definition bounded_object_fs_interval_matrix_scale_decimal_def:
  bounded_object_fs_interval_matrix_scale_decimal scalar [] =
      SOME (Num 0 : cv) /\
  bounded_object_fs_interval_matrix_scale_decimal scalar (row::rows) =
    case bounded_object_fs_interval_list_scale_decimal scalar row of
    | NONE => NONE
    | SOME scaled_row =>
      case bounded_object_fs_interval_matrix_scale_decimal scalar rows of
      | NONE => NONE
      | SOME scaled_rows => SOME (Pair scaled_row scaled_rows)
End

Theorem bounded_object_fs_interval_matrix_scale_decimal_exact:
  !result.
    bounded_interval64_matrix_scale_decimal scalar rows = SOME result ==>
    bounded_object_fs_interval_matrix_scale_decimal scalar rows =
      SOME (bounded_interval64_object_cv_matrix result)
Proof
  Induct_on `rows`
  >> rw [bounded_interval64_matrix_scale_decimal_def,
         bounded_object_fs_interval_matrix_scale_decimal_def,
         bounded_interval64_object_cv_matrix_def]
  >> every_case_tac
  >> gvs [bounded_interval64_object_cv_matrix_def]
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> res_tac
  >> gvs [bounded_interval64_object_cv_matrix_def]
QED

Definition bounded_interval64_matrix_add_def:
  bounded_interval64_matrix_add [] [] = SOME [] /\
  bounded_interval64_matrix_add [] (_::_) = NONE /\
  bounded_interval64_matrix_add (_::_) [] = NONE /\
  bounded_interval64_matrix_add (left::left_rows) (right::right_rows) =
    case bounded_interval64_list_add left right of
    | NONE => NONE
    | SOME row =>
      case bounded_interval64_matrix_add left_rows right_rows of
      | NONE => NONE
      | SOME rows => SOME (row::rows)
End

Definition bounded_object_fs_interval_matrix_add_def:
  bounded_object_fs_interval_matrix_add [] [] = SOME (Num 0 : cv) /\
  bounded_object_fs_interval_matrix_add [] (_::_) = NONE /\
  bounded_object_fs_interval_matrix_add (_::_) [] = NONE /\
  bounded_object_fs_interval_matrix_add (left::left_rows)
      (right::right_rows) =
    case bounded_object_fs_interval_list_add left right of
    | NONE => NONE
    | SOME row =>
      case bounded_object_fs_interval_matrix_add left_rows right_rows of
      | NONE => NONE
      | SOME rows => SOME (Pair row rows)
End

Theorem bounded_object_fs_interval_matrix_add_exact:
  !right result.
    bounded_interval64_matrix_add left right = SOME result ==>
    bounded_object_fs_interval_matrix_add left right =
      SOME (bounded_interval64_object_cv_matrix result)
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw [bounded_interval64_matrix_add_def,
         bounded_object_fs_interval_matrix_add_def,
         bounded_interval64_object_cv_matrix_def]
  >> every_case_tac
  >> gvs [bounded_interval64_object_cv_matrix_def]
  >> imp_res_tac bounded_object_fs_interval_list_add_exact
  >> res_tac
  >> gvs [bounded_interval64_object_cv_matrix_def]
QED

Theorem bounded_interval64_list_scale_decimal_relation:
  !result.
    bounded_interval64_list_scale_decimal scalar values = SOME result ==>
    LIST_REL
      (\value scaled.
         bounded_interval64_mul_decimal scalar value = SOME scaled)
      values result
Proof
  Induct_on `values`
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> gvs [LIST_REL_def]
QED

Theorem bounded_interval64_list_scale_decimal_from_relation:
  !scaled.
    LIST_REL
      (\value scaled.
         bounded_interval64_mul_decimal scalar value = SOME scaled)
      values scaled ==>
    bounded_interval64_list_scale_decimal scalar values = SOME scaled
Proof
  Induct_on `values`
  >> Cases_on `scaled`
  >> rw
       [LIST_REL_def,
        compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def]
  >> res_tac
  >> simp []
QED

Theorem bounded_interval64_matrix_scale_decimal_from_relation:
  !scaled_rows.
    LIST_REL
      (LIST_REL
        (\value scaled.
           bounded_interval64_mul_decimal scalar value = SOME scaled))
      rows scaled_rows ==>
    bounded_interval64_matrix_scale_decimal scalar rows = SOME scaled_rows
Proof
  Induct_on `rows`
  >> Cases_on `scaled_rows`
  >> rw [LIST_REL_def, bounded_interval64_matrix_scale_decimal_def]
  >> imp_res_tac bounded_interval64_list_scale_decimal_from_relation
  >> res_tac
  >> simp []
QED

Theorem bounded_hessian64_rows_scale_decimal:
  bounded_hessian64_rows hessian = SOME rows /\
  bounded_interval64_list_scale_decimal scalar hessian =
      SOME scaled_hessian /\
  bounded_hessian64_rows scaled_hessian = SOME scaled_rows ==>
  bounded_interval64_matrix_scale_decimal scalar rows = SOME scaled_rows
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_list_scale_decimal_relation
  >> irule bounded_interval64_matrix_scale_decimal_from_relation
  >> metis_tac
       [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_list_rel]
QED

Definition bounded_interval64_lists_add_def:
  bounded_interval64_lists_add [] [] [] = T /\
  bounded_interval64_lists_add (left::left_rest)
      (right::right_rest) (result::result_rest) =
    (bounded_interval64_add left right = SOME result /\
     bounded_interval64_lists_add left_rest right_rest result_rest) /\
  bounded_interval64_lists_add _ _ _ = F
End

Definition bounded_interval64_matrices_add_def:
  bounded_interval64_matrices_add [] [] [] = T /\
  bounded_interval64_matrices_add (left::left_rows)
      (right::right_rows) (result::result_rows) =
    (bounded_interval64_lists_add left right result /\
     bounded_interval64_matrices_add
       left_rows right_rows result_rows) /\
  bounded_interval64_matrices_add _ _ _ = F
End

Theorem bounded_interval64_list_add_relation:
  !right result.
    bounded_interval64_list_add left right = SOME result ==>
    bounded_interval64_lists_add left right result
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw [compute_boundedIntervalListTheory.bounded_interval64_list_add_def]
  >> every_case_tac
  >> gvs [bounded_interval64_lists_add_def]
  >> res_tac
  >> gvs [bounded_interval64_lists_add_def]
QED

Theorem bounded_interval64_list_add_from_relation:
  bounded_interval64_lists_add left right result ==>
  bounded_interval64_list_add left right = SOME result
Proof
  map_every qid_spec_tac [`result`, `right`, `left`]
  >> Induct
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [bounded_interval64_lists_add_def,
         compute_boundedIntervalListTheory.bounded_interval64_list_add_def]
  >> res_tac
  >> simp []
QED

Theorem bounded_interval64_matrix_add_from_relation:
  bounded_interval64_matrices_add left right result ==>
  bounded_interval64_matrix_add left right = SOME result
Proof
  map_every qid_spec_tac [`result`, `right`, `left`]
  >> Induct
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [bounded_interval64_matrices_add_def,
         bounded_interval64_matrix_add_def]
  >> imp_res_tac bounded_interval64_list_add_from_relation
  >> res_tac
  >> simp []
QED

Theorem bounded_hessian64_rows_preserve_add_relation:
  bounded_hessian64_rows left = SOME left_rows /\
  bounded_hessian64_rows right = SOME right_rows /\
  bounded_hessian64_rows result = SOME result_rows /\
  bounded_interval64_lists_add left right result ==>
  bounded_interval64_matrices_add left_rows right_rows result_rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs [bounded_interval64_lists_add_def,
          bounded_interval64_matrices_add_def]
QED

Theorem bounded_hessian64_rows_add:
  bounded_hessian64_rows left = SOME left_rows /\
  bounded_hessian64_rows right = SOME right_rows /\
  bounded_interval64_list_add left right = SOME result /\
  bounded_hessian64_rows result = SOME result_rows ==>
  bounded_interval64_matrix_add left_rows right_rows = SOME result_rows
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_list_add_relation
  >> irule bounded_interval64_matrix_add_from_relation
  >> metis_tac [bounded_hessian64_rows_preserve_add_relation]
QED

Theorem bounded_object_hessian64_rows_scale_decimal_exact:
  bounded_hessian64_rows hessian = SOME rows /\
  bounded_interval64_list_scale_decimal scalar hessian =
      SOME scaled_hessian /\
  bounded_hessian64_rows scaled_hessian = SOME scaled_rows ==>
  bounded_object_fs_interval_matrix_scale_decimal scalar rows =
    SOME (bounded_interval64_object_cv_matrix scaled_rows)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_matrix_scale_decimal_exact
  >> metis_tac [bounded_hessian64_rows_scale_decimal]
QED

Theorem bounded_object_hessian64_rows_add_exact:
  bounded_hessian64_rows left = SOME left_rows /\
  bounded_hessian64_rows right = SOME right_rows /\
  bounded_interval64_list_add left right = SOME result /\
  bounded_hessian64_rows result = SOME result_rows ==>
  bounded_object_fs_interval_matrix_add left_rows right_rows =
    SOME (bounded_interval64_object_cv_matrix result_rows)
Proof
  strip_tac
  >> irule bounded_object_fs_interval_matrix_add_exact
  >> metis_tac [bounded_hessian64_rows_add]
QED

Definition bounded_object_case10173_defer_def:
  bounded_object_case10173_defer
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    Pair (bounded_bool_object_cv domain)
      (Pair
        (Pair (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv_list center_gradient))
        (Pair (bounded_interval64_object_cv bounded_interval64_zero)
          (Pair
            (bounded_interval64_object_cv_list
              (bounded_interval64_zeros 6))
            (bounded_interval64_object_cv_list hessian))))
End

Theorem bounded_object_case10173_defer_exact:
  bounded_case10173_defer source = SOME result ==>
  bounded_object_case10173_defer source =
    bounded_taylor64_flat_object_cv result
Proof
  Cases_on `source`
  >> rw
       [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_defer_def,
        bounded_object_case10173_defer_def,
        bounded_taylor64_flat_object_cv_def]
  >> every_case_tac
  >> gvs [compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
          LET_THM]
  >> simp [bounded_taylor64_flat_object_cv_def]
QED

Definition bounded_object_case10173_deferred_scale_decimal_def:
  bounded_object_case10173_deferred_scale_decimal coefficient
      (BoundedTaylor64 domain center_value center_gradient
        value_bound gradient_bounds hessian) =
    case bounded_object_fs_interval_mul_decimal
      (bounded_interval64_object_cv coefficient)
      (bounded_interval64_object_cv center_value) of
    | NONE => NONE
    | SOME scaled_value =>
      case bounded_object_fs_interval_list_scale_decimal
        coefficient center_gradient of
      | NONE => NONE
      | SOME scaled_gradient =>
        case bounded_object_fs_interval_list_scale_decimal
          coefficient hessian of
        | NONE => NONE
        | SOME scaled_hessian =>
            SOME
              (Pair (bounded_bool_object_cv domain)
                (Pair
                  (Pair scaled_value scaled_gradient)
                  (Pair
                    (bounded_interval64_object_cv bounded_interval64_zero)
                    (Pair
                      (bounded_interval64_object_cv_list
                        (bounded_interval64_zeros 6))
                      scaled_hessian))))
End

Theorem bounded_object_case10173_deferred_scale_decimal_exact:
  bounded_case10173_deferred_scale_decimal coefficient source =
      SOME result ==>
  bounded_object_case10173_deferred_scale_decimal coefficient source =
    SOME (bounded_taylor64_flat_object_cv result)
Proof
  Cases_on `source`
  >> rw
       [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_deferred_scale_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> imp_res_tac
       compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_exact
  >> gvs
       [bounded_object_case10173_deferred_scale_decimal_def,
        bounded_taylor64_flat_object_cv_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_make_def,
        LET_THM]
QED

Definition bounded_object_case10173_deferred_add_def:
  bounded_object_case10173_deferred_add
      (BoundedTaylor64 left_domain left_center_value left_center_gradient
        left_value_bound left_gradient_bounds left_hessian)
      (BoundedTaylor64 right_domain right_center_value right_center_gradient
        right_value_bound right_gradient_bounds right_hessian) =
    case bounded_object_fs_interval_add
      (bounded_interval64_object_cv left_center_value)
      (bounded_interval64_object_cv right_center_value) of
    | NONE => NONE
    | SOME center_value =>
      case bounded_object_fs_interval_list_add
        left_center_gradient right_center_gradient of
      | NONE => NONE
      | SOME center_gradient =>
        case bounded_object_fs_interval_add
          (bounded_interval64_object_cv left_value_bound)
          (bounded_interval64_object_cv right_value_bound) of
        | NONE => NONE
        | SOME value_bound =>
          case bounded_object_fs_interval_list_add
            left_gradient_bounds right_gradient_bounds of
          | NONE => NONE
          | SOME gradient_bounds =>
            case bounded_object_fs_interval_list_add
              left_hessian right_hessian of
            | NONE => NONE
            | SOME hessian =>
                SOME
                  (Pair (bounded_bool_object_cv
                           (left_domain /\ right_domain))
                    (Pair (Pair center_value center_gradient)
                      (Pair value_bound
                        (Pair gradient_bounds hessian))))
End

Theorem bounded_object_case10173_deferred_add_exact:
  bounded_case10173_deferred_add left right = SOME result ==>
  bounded_object_case10173_deferred_add left right =
    SOME (bounded_taylor64_flat_object_cv result)
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_deferred_add_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_add_def,
        compute_boundedTaylorStateTheory.bounded_taylor64_add_unchecked_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact
  >> imp_res_tac bounded_object_fs_interval_list_add_exact
  >> gvs
       [bounded_object_case10173_deferred_add_def,
        bounded_taylor64_flat_object_cv_def]
QED

Theorem bounded_object_case10173_complete_deferred_decimal_exact:
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_case10173_complete_deferred_decimal radii
      (BoundedTaylor64 result_domain center_value center_gradient
        value_bound gradient_bounds hessian) = SOME result ==>
  bounded_object_fs_taylor_complete radii result_domain center_value
      center_gradient hessian hessian_rows =
    SOME (bounded_taylor64_rows_object_cv result hessian_rows)
Proof
  rw
    [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_complete_deferred_decimal_def]
  >> metis_tac [bounded_object_fs_taylor_complete_exact]
QED

val _ = export_theory ();
