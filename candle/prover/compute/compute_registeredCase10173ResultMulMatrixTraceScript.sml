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
  compute_registeredCase10173HistoricalDeltaX4ValueBlockEval
  compute_registeredCase10173HistoricalSecondOrderBoxEval
Libs
  bossLib preamble

Theorem registered_case10173_raw_product_ints_comm:
  registered_case10173_raw_product_ints left right =
  registered_case10173_raw_product_ints right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> rw
       [compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_raw_product_ints_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_int_min4_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_int_max4_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_int_min_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_int_max_def]
  >> every_case_tac
  >> fs []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_raw_interval_endpoint_equiv_def:
  registered_case10173_raw_interval_endpoint_equiv left right <=>
    ?lower upper.
      bounded_object_interval_ints left = SOME (lower,upper) /\
      bounded_object_interval_ints right = SOME (lower,upper)
End

Theorem registered_case10173_raw_interval_add_endpoint_values:
  bounded_object_interval_ints left = SOME (left_lower,left_upper) /\
  bounded_object_interval_ints right = SOME (right_lower,right_upper) /\
  bounded_object_fs_raw_interval_add left right = SOME result ==>
  bounded_object_interval_ints result =
    SOME (left_lower + right_lower,left_upper + right_upper)
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL
         [`left`,`right`,`left_lower`,`left_upper`,
          `right_lower`,`right_upper`]
         bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `computed` strip_assume_tac)
  >> gvs []
QED

Theorem registered_case10173_raw_product_swapped_endpoint_equiv:
  bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv left)
      (bounded_interval64_object_cv right) = SOME forward /\
  bounded_object_fs_raw_interval_mul
      (bounded_interval64_object_cv right)
      (bounded_interval64_object_cv left) = SOME backward ==>
  registered_case10173_raw_interval_endpoint_equiv forward backward
Proof
  strip_tac
  >> imp_res_tac registered_case10173_raw_product_endpoint_values
  >> rw [registered_case10173_raw_interval_endpoint_equiv_def]
  >> Cases_on `registered_case10173_raw_product_ints left right`
  >> qexists_tac `q`
  >> qexists_tac `r`
  >> simp [registered_case10173_raw_product_ints_comm]
QED

Theorem registered_case10173_raw_four_tree_middle_swap_endpoint_equiv:
  bounded_object_interval_ints scaled_left =
      SOME (scaled_left_lower,scaled_left_upper) /\
  registered_case10173_raw_interval_endpoint_equiv
      left_outer historical_right_outer /\
  registered_case10173_raw_interval_endpoint_equiv
      right_outer historical_left_outer /\
  bounded_object_interval_ints scaled_right =
      SOME (scaled_right_lower,scaled_right_upper) /\
  bounded_object_fs_raw_interval_add scaled_left left_outer =
      SOME compact_left_half /\
  bounded_object_fs_raw_interval_add right_outer scaled_right =
      SOME compact_right_half /\
  bounded_object_fs_raw_interval_add compact_left_half compact_right_half =
      SOME compact_sum /\
  bounded_object_fs_raw_interval_add scaled_left historical_left_outer =
      SOME historical_left_half /\
  bounded_object_fs_raw_interval_add historical_right_outer scaled_right =
      SOME historical_right_half /\
  bounded_object_fs_raw_interval_add historical_left_half historical_right_half =
      SOME historical_sum ==>
  registered_case10173_raw_interval_endpoint_equiv
      compact_sum historical_sum
Proof
  strip_tac
  >> qpat_x_assum
       `registered_case10173_raw_interval_endpoint_equiv
          left_outer historical_right_outer` mp_tac
  >> simp [registered_case10173_raw_interval_endpoint_equiv_def]
  >> disch_then
       (qx_choose_then `left_outer_lower`
         (qx_choose_then `left_outer_upper` strip_assume_tac))
  >> qpat_x_assum
       `registered_case10173_raw_interval_endpoint_equiv
          right_outer historical_left_outer` mp_tac
  >> simp [registered_case10173_raw_interval_endpoint_equiv_def]
  >> disch_then
       (qx_choose_then `right_outer_lower`
         (qx_choose_then `right_outer_upper` strip_assume_tac))
  >> imp_res_tac registered_case10173_raw_interval_add_endpoint_values
  >> qexists_tac
       `scaled_left_lower + left_outer_lower +
        (right_outer_lower + scaled_right_lower)`
  >> qexists_tac
       `scaled_left_upper + left_outer_upper +
        (right_outer_upper + scaled_right_upper)`
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_raw_product_relation_def:
  registered_case10173_raw_product_relation left right raw <=>
    bounded_object_interval_ints raw =
      SOME (registered_case10173_raw_product_ints left right)
End

Definition registered_case10173_raw_interval_object_def:
  registered_case10173_raw_interval_object value <=>
    ?lower upper.
      bounded_object_interval_ints value = SOME (lower,upper)
End

Theorem registered_case10173_raw_product_relation_object:
  registered_case10173_raw_product_relation left right raw ==>
  registered_case10173_raw_interval_object raw
Proof
  rw [registered_case10173_raw_product_relation_def,
      registered_case10173_raw_interval_object_def]
  >> Cases_on `registered_case10173_raw_product_ints left right`
  >> metis_tac []
QED

Theorem registered_case10173_raw_product_relations_endpoint_equiv:
  registered_case10173_raw_product_relation left right first_raw /\
  registered_case10173_raw_product_relation left right second_raw ==>
  registered_case10173_raw_interval_endpoint_equiv first_raw second_raw
Proof
  rw [registered_case10173_raw_product_relation_def,
      registered_case10173_raw_interval_endpoint_equiv_def]
  >> Cases_on `registered_case10173_raw_product_ints left right`
  >> metis_tac []
QED

Theorem registered_case10173_raw_product_relations_swapped_endpoint_equiv:
  registered_case10173_raw_product_relation left right forward /\
  registered_case10173_raw_product_relation right left backward ==>
  registered_case10173_raw_interval_endpoint_equiv forward backward
Proof
  rw [registered_case10173_raw_product_relation_def,
      registered_case10173_raw_interval_endpoint_equiv_def]
  >> Cases_on `registered_case10173_raw_product_ints left right`
  >> qexists_tac `q`
  >> qexists_tac `r`
  >> simp [registered_case10173_raw_product_ints_comm]
QED

Theorem registered_case10173_raw_list_scale_typed_trace:
  !values.
    ?raw_values.
      registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv scalar)
          (MAP bounded_interval64_object_cv values) = SOME raw_values /\
      LIST_REL
        (\value raw.
           registered_case10173_raw_product_relation scalar value raw)
        values raw_values
Proof
  Induct
  >- simp
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def]
  >> gen_tac
  >> mp_tac
       (Q.SPECL [`scalar`,`h`] registered_case10173_raw_product_exists)
  >> disch_then (qx_choose_then `raw_head` strip_assume_tac)
  >> qpat_x_assum `?raw_values. _`
       (qx_choose_then `raw_tail` strip_assume_tac)
  >> qexists_tac `raw_head::raw_tail`
  >> imp_res_tac registered_case10173_raw_product_endpoint_values
  >> simp
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
        registered_case10173_raw_product_relation_def,
        LIST_REL_def]
QED

Theorem registered_case10173_raw_outer_typed_trace:
  !left.
    ?raw_rows.
      registered_case10173_fs_raw_interval_outer_object
          (MAP bounded_interval64_object_cv left)
          (MAP bounded_interval64_object_cv right) = SOME raw_rows /\
      LIST_REL
        (\left_value raw_row.
           LIST_REL
             (\right_value raw.
                registered_case10173_raw_product_relation
                  left_value right_value raw)
             right raw_row)
        left raw_rows
Proof
  Induct
  >- simp
       [compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_def]
  >> gen_tac
  >> mp_tac
       (Q.INST [`scalar` |-> `h`]
          (Q.SPEC `right`
            registered_case10173_raw_list_scale_typed_trace))
  >> disch_then (qx_choose_then `raw_row` strip_assume_tac)
  >> qpat_x_assum `?raw_rows. _`
       (qx_choose_then `raw_rows` strip_assume_tac)
  >> qexists_tac `raw_row::raw_rows`
  >> simp
       [compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_def,
        LIST_REL_def]
QED

Theorem registered_case10173_raw_product_relation_list_objects:
  !values raw_values.
    LIST_REL
      (\value raw.
         registered_case10173_raw_product_relation scalar value raw)
      values raw_values ==>
    EVERY registered_case10173_raw_interval_object raw_values
Proof
  Induct
  >> Cases_on `raw_values`
  >> rw [LIST_REL_def]
  >> imp_res_tac registered_case10173_raw_product_relation_object
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_raw_product_relation_matrix_objects:
  !left raw_rows.
    LIST_REL
      (\left_value raw_row.
         LIST_REL
           (\right_value raw.
              registered_case10173_raw_product_relation
                left_value right_value raw)
           right raw_row)
      left raw_rows ==>
    EVERY (EVERY registered_case10173_raw_interval_object) raw_rows
Proof
  Induct
  >> Cases_on `raw_rows`
  >> rw [LIST_REL_def]
  >> imp_res_tac registered_case10173_raw_product_relation_list_objects
  >> res_tac
  >> simp []
QED

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

Theorem registered_case10173_raw_interval_add_objects:
  registered_case10173_raw_interval_object left /\
  registered_case10173_raw_interval_object right ==>
  ?result.
    bounded_object_fs_raw_interval_add left right = SOME result /\
    registered_case10173_raw_interval_object result
Proof
  rw [registered_case10173_raw_interval_object_def]
  >> mp_tac
       (Q.SPECL
         [`left`,`right`,`lower`,`upper`,`lower'`,`upper'`]
         bounded_object_fs_raw_interval_add_ints_exists)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `result` strip_assume_tac)
  >> qexists_tac `result`
  >> simp [registered_case10173_raw_interval_object_def]
QED

Theorem registered_case10173_raw_list_add_objects:
  !left right.
    EVERY registered_case10173_raw_interval_object left /\
    EVERY registered_case10173_raw_interval_object right /\
    LENGTH left = LENGTH right ==>
    ?result.
      registered_case10173_raw_lists_add left right result /\
      EVERY registered_case10173_raw_interval_object result
Proof
  Induct
  >- (Cases_on `right`
      >> rw []
      >> qexists_tac `[]`
      >> simp [registered_case10173_raw_lists_add_def])
  >> rpt gen_tac
  >> Cases_on `right`
  >> rw []
  >> mp_tac
       (Q.INST [`left` |-> `h`, `right` |-> `h'`]
          registered_case10173_raw_interval_add_objects)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_head` strip_assume_tac)
  >> first_x_assum (mp_tac o Q.SPEC `t`)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_tail` strip_assume_tac)
  >> qexists_tac `raw_head::raw_tail`
  >> simp [registered_case10173_raw_lists_add_def]
QED

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

Theorem registered_case10173_raw_matrix_add_objects:
  !left right.
    EVERY (EVERY registered_case10173_raw_interval_object) left /\
    EVERY (EVERY registered_case10173_raw_interval_object) right /\
    LIST_REL (\left_row right_row.
      LENGTH left_row = LENGTH right_row) left right ==>
    ?result.
      registered_case10173_raw_matrices_add left right result /\
      EVERY (EVERY registered_case10173_raw_interval_object) result
Proof
  Induct
  >- (Cases_on `right`
      >> rw [LIST_REL_def]
      >> qexists_tac `[]`
      >> simp [registered_case10173_raw_matrices_add_def])
  >> rpt gen_tac
  >> Cases_on `right`
  >> rw [LIST_REL_def]
  >> mp_tac
       (Q.SPECL [`h`,`h'`] registered_case10173_raw_list_add_objects)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_row` strip_assume_tac)
  >> first_x_assum (mp_tac o Q.SPEC `t`)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `raw_rows` strip_assume_tac)
  >> qexists_tac `raw_row::raw_rows`
  >> simp [registered_case10173_raw_matrices_add_def]
QED

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
