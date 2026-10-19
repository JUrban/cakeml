(*****************************************************************************
 * Compact-to-matrix raw traces for the historical Taylor product.
 *
 * The fast checker retains the 21 independent entries of a symmetric
 * Hessian.  The authenticated source expands those entries to six rows
 * before applying its raw arithmetic.  These generic lemmas show that raw
 * scale, add, and final round commute with that fixed expansion.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulMatrixTrace
Ancestors
  compute_registeredCase10173ResultMulTypedTrace
  compute_registeredCase10173HistoricalSecondOrderBoxEval
Libs
  bossLib preamble

Theorem registered_case10173_bounded_hessian64_rows_map:
  bounded_hessian64_rows values = SOME rows ==>
  bounded_hessian64_rows (MAP f values) = SOME (MAP (MAP f) rows)
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_raw_list_scale_relation:
  !values products.
    registered_case10173_fs_raw_interval_list_scale_object
        scalar values = SOME products ==>
    LIST_REL
      (\value product.
         bounded_object_fs_raw_interval_mul scalar value = SOME product)
      values products
Proof
  Induct
  >> rw
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> gvs [LIST_REL_def]
QED

Theorem registered_case10173_raw_list_scale_from_relation:
  !products.
    LIST_REL
      (\value product.
         bounded_object_fs_raw_interval_mul scalar value = SOME product)
      values products ==>
    registered_case10173_fs_raw_interval_list_scale_object
        scalar values = SOME products
Proof
  Induct_on `values`
  >> Cases_on `products`
  >> rw
       [LIST_REL_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def]
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_raw_matrix_scale_from_relation:
  !products.
    LIST_REL
      (LIST_REL
        (\value product.
           bounded_object_fs_raw_interval_mul scalar value = SOME product))
      rows products ==>
    registered_case10173_fs_raw_interval_matrix_scale_object
        scalar rows = SOME products
Proof
  Induct_on `rows`
  >> Cases_on `products`
  >> rw
       [LIST_REL_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_scale_object_def]
  >> imp_res_tac registered_case10173_raw_list_scale_from_relation
  >> res_tac
  >> simp []
QED

Definition registered_case10173_raw_lists_add_def:
  registered_case10173_raw_lists_add [] [] [] = T /\
  registered_case10173_raw_lists_add
      (left::left_rest) (right::right_rest) (result::result_rest) =
    (bounded_object_fs_raw_interval_add left right = SOME result /\
     registered_case10173_raw_lists_add
       left_rest right_rest result_rest) /\
  registered_case10173_raw_lists_add _ _ _ = F
End

Theorem registered_case10173_raw_list_add_relation:
  !right result.
    registered_case10173_fs_raw_interval_list_add_object
        left right = SOME result ==>
    registered_case10173_raw_lists_add left right result
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> rw
       [compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_def]
  >> every_case_tac
  >> gvs [registered_case10173_raw_lists_add_def]
  >> res_tac
  >> gvs [registered_case10173_raw_lists_add_def]
QED

Theorem registered_case10173_raw_list_add_from_relation:
  !right result.
    registered_case10173_raw_lists_add left right result ==>
    registered_case10173_fs_raw_interval_list_add_object
        left right = SOME result
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw
       [registered_case10173_raw_lists_add_def,
        compute_registeredCase10173HistoricalRawListAddEvalTheory.registered_case10173_fs_raw_interval_list_add_object_def]
  >> res_tac
  >> simp []
QED

Definition registered_case10173_raw_matrices_add_def:
  registered_case10173_raw_matrices_add [] [] [] = T /\
  registered_case10173_raw_matrices_add
      (left::left_rows) (right::right_rows) (result::result_rows) =
    (registered_case10173_raw_lists_add left right result /\
     registered_case10173_raw_matrices_add
       left_rows right_rows result_rows) /\
  registered_case10173_raw_matrices_add _ _ _ = F
End

Theorem registered_case10173_raw_matrix_add_from_relation:
  !right result.
    registered_case10173_raw_matrices_add left right result ==>
    registered_case10173_fs_raw_interval_matrix_add_object
        left right = SOME result
Proof
  Induct_on `left`
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw
       [registered_case10173_raw_matrices_add_def,
        compute_registeredCase10173HistoricalRawMatrixAddEvalTheory.registered_case10173_fs_raw_interval_matrix_add_object_def]
  >> imp_res_tac registered_case10173_raw_list_add_from_relation
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_bounded_hessian64_rows_preserve_raw_add:
  bounded_hessian64_rows left = SOME left_rows /\
  bounded_hessian64_rows right = SOME right_rows /\
  bounded_hessian64_rows result = SOME result_rows /\
  registered_case10173_raw_lists_add left right result ==>
  registered_case10173_raw_matrices_add left_rows right_rows result_rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs [registered_case10173_raw_lists_add_def,
          registered_case10173_raw_matrices_add_def]
QED

Theorem registered_case10173_raw_hessian_add_rows:
  bounded_hessian64_rows left = SOME left_rows /\
  bounded_hessian64_rows right = SOME right_rows /\
  bounded_hessian64_rows result = SOME result_rows /\
  registered_case10173_fs_raw_interval_list_add_object
      left right = SOME result ==>
  registered_case10173_fs_raw_interval_matrix_add_object
      left_rows right_rows = SOME result_rows
Proof
  strip_tac
  >> imp_res_tac registered_case10173_raw_list_add_relation
  >> irule registered_case10173_raw_matrix_add_from_relation
  >> metis_tac
       [registered_case10173_bounded_hessian64_rows_preserve_raw_add]
QED

Theorem registered_case10173_raw_list_round_relation:
  !values rounded.
    registered_case10173_fs_raw_interval_list_round_object
        denominator values = SOME rounded ==>
    LIST_REL
      (\value result.
         bounded_object_fs_raw_interval_round denominator value = SOME result)
      values rounded
Proof
  Induct
  >> rw
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> gvs [LIST_REL_def]
QED

Theorem registered_case10173_raw_list_round_from_relation:
  !rounded.
    LIST_REL
      (\value result.
         bounded_object_fs_raw_interval_round denominator value = SOME result)
      values rounded ==>
    registered_case10173_fs_raw_interval_list_round_object
        denominator values = SOME rounded
Proof
  Induct_on `values`
  >> Cases_on `rounded`
  >> rw
       [LIST_REL_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def]
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_raw_matrix_round_from_relation:
  !rounded.
    LIST_REL
      (LIST_REL
        (\value result.
           bounded_object_fs_raw_interval_round denominator value = SOME result))
      rows rounded ==>
    registered_case10173_fs_raw_interval_matrix_round_object
        denominator rows = SOME rounded
Proof
  Induct_on `rows`
  >> Cases_on `rounded`
  >> rw
       [LIST_REL_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_round_object_def]
  >> imp_res_tac registered_case10173_raw_list_round_from_relation
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_raw_hessian_scale_rows:
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  registered_case10173_fs_raw_interval_list_scale_object
      scalar (MAP bounded_interval64_object_cv hessian) = SOME raw_hessian /\
  bounded_hessian64_rows raw_hessian = SOME raw_rows ==>
  registered_case10173_fs_raw_interval_matrix_scale_object
      scalar (MAP (MAP bounded_interval64_object_cv) hessian_rows) =
    SOME raw_rows
Proof
  strip_tac
  >> imp_res_tac registered_case10173_raw_list_scale_relation
  >> imp_res_tac registered_case10173_bounded_hessian64_rows_map
  >> imp_res_tac
       compute_boundedTaylorGradientTheory.bounded_hessian64_rows_list_rel
  >> irule registered_case10173_raw_matrix_scale_from_relation
  >> metis_tac
       [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_list_rel,
        registered_case10173_bounded_hessian64_rows_map]
QED

Theorem registered_case10173_raw_hessian_round_rows:
  bounded_hessian64_rows raw_hessian = SOME raw_rows /\
  bounded_hessian64_rows rounded_hessian = SOME rounded_rows /\
  registered_case10173_fs_raw_interval_list_round_object
      denominator raw_hessian =
    SOME (MAP bounded_interval64_object_cv rounded_hessian) ==>
  registered_case10173_fs_raw_interval_matrix_round_object
      denominator raw_rows =
    SOME (MAP (MAP bounded_interval64_object_cv) rounded_rows)
Proof
  strip_tac
  >> imp_res_tac registered_case10173_raw_list_round_relation
  >> imp_res_tac registered_case10173_bounded_hessian64_rows_map
  >> imp_res_tac
       compute_boundedTaylorGradientTheory.bounded_hessian64_rows_list_rel
  >> irule registered_case10173_raw_matrix_round_from_relation
  >> metis_tac
       [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_list_rel,
        registered_case10173_bounded_hessian64_rows_map]
QED

val _ = export_theory ();
