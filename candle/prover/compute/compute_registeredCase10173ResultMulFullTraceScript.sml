(*****************************************************************************
 * Full compact-to-source Hessian trace for the historical Taylor product.
 *
 * The fast checker stores the upper triangle.  The historical source builds
 * both ordered gradient outer products as full matrices, so the two middle
 * terms exchange roles below the diagonal.  The generic list/matrix layer
 * below separates that local permutation fact from the fixed six-dimensional
 * triangular layout.
 *****************************************************************************)
Theory compute_registeredCase10173ResultMulFullTrace
Ancestors
  compute_registeredCase10173ResultMulMatrixTrace
Libs
  bossLib preamble

Definition registered_case10173_raw_outer_cell_aligned_def:
  registered_case10173_raw_outer_cell_aligned
      compact_left compact_right historical_left historical_right <=>
    (registered_case10173_raw_interval_endpoint_equiv
       compact_left historical_left /\
     registered_case10173_raw_interval_endpoint_equiv
       compact_right historical_right) \/
    (registered_case10173_raw_interval_endpoint_equiv
       compact_left historical_right /\
     registered_case10173_raw_interval_endpoint_equiv
       compact_right historical_left)
End

Definition registered_case10173_raw_outer_lists_aligned_def:
  registered_case10173_raw_outer_lists_aligned [] [] [] [] = T /\
  registered_case10173_raw_outer_lists_aligned
      (compact_left::compact_left_rest)
      (compact_right::compact_right_rest)
      (historical_left::historical_left_rest)
      (historical_right::historical_right_rest) =
    (registered_case10173_raw_outer_cell_aligned
       compact_left compact_right historical_left historical_right /\
     registered_case10173_raw_outer_lists_aligned
       compact_left_rest compact_right_rest
       historical_left_rest historical_right_rest) /\
  registered_case10173_raw_outer_lists_aligned _ _ _ _ = F
End

Definition registered_case10173_raw_outer_matrices_aligned_def:
  registered_case10173_raw_outer_matrices_aligned [] [] [] [] = T /\
  registered_case10173_raw_outer_matrices_aligned
      (compact_left::compact_left_rows)
      (compact_right::compact_right_rows)
      (historical_left::historical_left_rows)
      (historical_right::historical_right_rows) =
    (registered_case10173_raw_outer_lists_aligned
       compact_left compact_right historical_left historical_right /\
     registered_case10173_raw_outer_matrices_aligned
       compact_left_rows compact_right_rows
       historical_left_rows historical_right_rows) /\
  registered_case10173_raw_outer_matrices_aligned _ _ _ _ = F
End

Theorem registered_case10173_raw_outer_lists_aligned_lengths:
  !compact_left compact_right historical_left historical_right.
    registered_case10173_raw_outer_lists_aligned
      compact_left compact_right historical_left historical_right ==>
    LENGTH compact_left = LENGTH compact_right /\
    LENGTH compact_right = LENGTH historical_left /\
    LENGTH historical_left = LENGTH historical_right
Proof
  Induct
  >> Cases_on `compact_right`
  >> Cases_on `historical_left`
  >> Cases_on `historical_right`
  >> rw [registered_case10173_raw_outer_lists_aligned_def]
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_raw_outer_matrices_aligned_lengths:
  !compact_left compact_right historical_left historical_right.
    registered_case10173_raw_outer_matrices_aligned
      compact_left compact_right historical_left historical_right ==>
    LENGTH compact_left = LENGTH compact_right /\
    LENGTH compact_right = LENGTH historical_left /\
    LENGTH historical_left = LENGTH historical_right
Proof
  Induct
  >> Cases_on `compact_right`
  >> Cases_on `historical_left`
  >> Cases_on `historical_right`
  >> rw [registered_case10173_raw_outer_matrices_aligned_def]
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_raw_lists_add_lengths:
  !left right result.
    registered_case10173_raw_lists_add left right result ==>
    LENGTH left = LENGTH right /\ LENGTH right = LENGTH result
Proof
  Induct
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [registered_case10173_raw_lists_add_def]
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_raw_matrices_add_lengths:
  !left right result.
    registered_case10173_raw_matrices_add left right result ==>
    LENGTH left = LENGTH right /\ LENGTH right = LENGTH result
Proof
  Induct
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [registered_case10173_raw_matrices_add_def]
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_raw_matrices_add_preserves_width:
  !left right result.
    registered_case10173_raw_matrices_add left right result /\
    EVERY (\row. LENGTH row = width) left /\
    EVERY (\row. LENGTH row = width) right ==>
    EVERY (\row. LENGTH row = width) result
Proof
  Induct
  >> Cases_on `right`
  >> Cases_on `result`
  >> rw [registered_case10173_raw_matrices_add_def]
  >> imp_res_tac registered_case10173_raw_lists_add_lengths
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_raw_hessian_cell_endpoint_equiv:
  registered_case10173_raw_interval_object scaled_left /\
  registered_case10173_raw_interval_object scaled_right /\
  registered_case10173_raw_outer_cell_aligned
      compact_left_outer compact_right_outer
      historical_left_outer historical_right_outer /\
  bounded_object_fs_raw_interval_add scaled_left compact_left_outer =
      SOME compact_left_half /\
  bounded_object_fs_raw_interval_add compact_right_outer scaled_right =
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
       `registered_case10173_raw_interval_object scaled_left` mp_tac
  >> simp [registered_case10173_raw_interval_object_def]
  >> disch_then
       (qx_choose_then `scaled_left_lower`
         (qx_choose_then `scaled_left_upper` strip_assume_tac))
  >> qpat_x_assum
       `registered_case10173_raw_interval_object scaled_right` mp_tac
  >> simp [registered_case10173_raw_interval_object_def]
  >> disch_then
       (qx_choose_then `scaled_right_lower`
         (qx_choose_then `scaled_right_upper` strip_assume_tac))
  >> qpat_x_assum
       `registered_case10173_raw_outer_cell_aligned
          compact_left_outer compact_right_outer
          historical_left_outer historical_right_outer` mp_tac
  >> simp [registered_case10173_raw_outer_cell_aligned_def]
  >> disch_then (fn th => DISJ_CASES_TAC th)
  >- (match_mp_tac
        (Q.INST
          [`left_outer` |-> `compact_left_outer`,
           `right_outer` |-> `compact_right_outer`]
          registered_case10173_raw_four_tree_endpoint_equiv)
      >> asm_rewrite_tac [])
  >> match_mp_tac
       (Q.INST
         [`left_outer` |-> `compact_left_outer`,
          `right_outer` |-> `compact_right_outer`]
         registered_case10173_raw_four_tree_middle_swap_endpoint_equiv)
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_raw_hessian_lists_endpoint_equiv:
  !scaled_left compact_left_outer compact_right_outer scaled_right
   compact_left_half compact_right_half compact_sum historical_left_outer
   historical_right_outer historical_left_half historical_right_half
   historical_sum.
    EVERY registered_case10173_raw_interval_object scaled_left /\
    EVERY registered_case10173_raw_interval_object scaled_right /\
    registered_case10173_raw_outer_lists_aligned
      compact_left_outer compact_right_outer
      historical_left_outer historical_right_outer /\
    registered_case10173_raw_lists_add
      scaled_left compact_left_outer compact_left_half /\
    registered_case10173_raw_lists_add
      compact_right_outer scaled_right compact_right_half /\
    registered_case10173_raw_lists_add
      compact_left_half compact_right_half compact_sum /\
    registered_case10173_raw_lists_add
      scaled_left historical_left_outer historical_left_half /\
    registered_case10173_raw_lists_add
      historical_right_outer scaled_right historical_right_half /\
    registered_case10173_raw_lists_add
      historical_left_half historical_right_half historical_sum ==>
    LIST_REL registered_case10173_raw_interval_endpoint_equiv
      compact_sum historical_sum
Proof
  Induct_on `scaled_left`
  >> rpt gen_tac
  >> strip_tac
  >> imp_res_tac registered_case10173_raw_outer_lists_aligned_lengths
  >> imp_res_tac registered_case10173_raw_lists_add_lengths
  >> Cases_on `compact_left_outer` >> gvs []
  >> Cases_on `compact_right_outer` >> gvs []
  >> Cases_on `scaled_right` >> gvs []
  >> Cases_on `compact_left_half` >> gvs []
  >> Cases_on `compact_right_half` >> gvs []
  >> Cases_on `compact_sum` >> gvs []
  >> Cases_on `historical_left_outer` >> gvs []
  >> Cases_on `historical_right_outer` >> gvs []
  >> Cases_on `historical_left_half` >> gvs []
  >> Cases_on `historical_right_half` >> gvs []
  >> Cases_on `historical_sum` >> gvs []
  >> fs
       [registered_case10173_raw_outer_lists_aligned_def,
        registered_case10173_raw_lists_add_def,LIST_REL_def]
  >> imp_res_tac registered_case10173_raw_hessian_cell_endpoint_equiv
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_raw_hessian_matrices_endpoint_equiv:
  !scaled_left compact_left_outer compact_right_outer scaled_right
   compact_left_half compact_right_half compact_sum historical_left_outer
   historical_right_outer historical_left_half historical_right_half
   historical_sum.
    EVERY (EVERY registered_case10173_raw_interval_object) scaled_left /\
    EVERY (EVERY registered_case10173_raw_interval_object) scaled_right /\
    registered_case10173_raw_outer_matrices_aligned
      compact_left_outer compact_right_outer
      historical_left_outer historical_right_outer /\
    registered_case10173_raw_matrices_add
      scaled_left compact_left_outer compact_left_half /\
    registered_case10173_raw_matrices_add
      compact_right_outer scaled_right compact_right_half /\
    registered_case10173_raw_matrices_add
      compact_left_half compact_right_half compact_sum /\
    registered_case10173_raw_matrices_add
      scaled_left historical_left_outer historical_left_half /\
    registered_case10173_raw_matrices_add
      historical_right_outer scaled_right historical_right_half /\
    registered_case10173_raw_matrices_add
      historical_left_half historical_right_half historical_sum ==>
    LIST_REL
      (LIST_REL registered_case10173_raw_interval_endpoint_equiv)
      compact_sum historical_sum
Proof
  Induct_on `scaled_left`
  >> rpt gen_tac
  >> strip_tac
  >> imp_res_tac registered_case10173_raw_outer_matrices_aligned_lengths
  >> imp_res_tac registered_case10173_raw_matrices_add_lengths
  >> Cases_on `compact_left_outer` >> gvs []
  >> Cases_on `compact_right_outer` >> gvs []
  >> Cases_on `scaled_right` >> gvs []
  >> Cases_on `compact_left_half` >> gvs []
  >> Cases_on `compact_right_half` >> gvs []
  >> Cases_on `compact_sum` >> gvs []
  >> Cases_on `historical_left_outer` >> gvs []
  >> Cases_on `historical_right_outer` >> gvs []
  >> Cases_on `historical_left_half` >> gvs []
  >> Cases_on `historical_right_half` >> gvs []
  >> Cases_on `historical_sum` >> gvs []
  >> fs
       [registered_case10173_raw_outer_matrices_aligned_def,
        registered_case10173_raw_matrices_add_def,LIST_REL_def]
  >> imp_res_tac registered_case10173_raw_hessian_lists_endpoint_equiv
  >> res_tac
  >> simp []
QED

Theorem registered_case10173_raw_outer_source_rows_aligned:
  bounded_interval64_symmetric_product_pairs
      [left0;left1;left2;left3;left4;left5]
      [right0;right1;right2;right3;right4;right5] = SOME outer_pairs /\
  LIST_REL
      (\outer raw.
         registered_case10173_raw_product_relation
           (FST (FST outer)) (SND (FST outer)) raw)
      outer_pairs compact_left_outer /\
  LIST_REL
      (\outer raw.
         registered_case10173_raw_product_relation
           (FST (SND outer)) (SND (SND outer)) raw)
      outer_pairs compact_right_outer /\
  bounded_hessian64_rows compact_left_outer = SOME compact_left_rows /\
  bounded_hessian64_rows compact_right_outer = SOME compact_right_rows /\
  LIST_REL
      (\left_value raw_row.
         LIST_REL
           (\right_value raw.
              registered_case10173_raw_product_relation
                left_value right_value raw)
           [right0;right1;right2;right3;right4;right5] raw_row)
      [left0;left1;left2;left3;left4;left5] historical_left_outer /\
  LIST_REL
      (\right_value raw_row.
         LIST_REL
           (\left_value raw.
              registered_case10173_raw_product_relation
                right_value left_value raw)
           [left0;left1;left2;left3;left4;left5] raw_row)
      [right0;right1;right2;right3;right4;right5] historical_right_outer ==>
  registered_case10173_raw_outer_matrices_aligned
    compact_left_rows compact_right_rows
    historical_left_outer historical_right_outer
Proof
  rw
    [compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_def,
     compute_boundedTaylorMulTheory.bounded_interval64_symmetric_product_pairs_row_def]
  >> gvs
       [LIST_REL_def,
        compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def,
        registered_case10173_raw_outer_matrices_aligned_def,
        registered_case10173_raw_outer_lists_aligned_def,
        registered_case10173_raw_outer_cell_aligned_def]
  >> rpt conj_tac
  >> metis_tac
       [registered_case10173_raw_product_relations_endpoint_equiv,
        registered_case10173_raw_product_relations_swapped_endpoint_equiv]
QED

Theorem registered_case10173_raw_outer_source_rows_aligned_length6:
  LENGTH left = 6 /\ LENGTH right = 6 /\
  bounded_interval64_symmetric_product_pairs left right = SOME outer_pairs /\
  LIST_REL
      (\outer raw.
         registered_case10173_raw_product_relation
           (FST (FST outer)) (SND (FST outer)) raw)
      outer_pairs compact_left_outer /\
  LIST_REL
      (\outer raw.
         registered_case10173_raw_product_relation
           (FST (SND outer)) (SND (SND outer)) raw)
      outer_pairs compact_right_outer /\
  bounded_hessian64_rows compact_left_outer = SOME compact_left_rows /\
  bounded_hessian64_rows compact_right_outer = SOME compact_right_rows /\
  LIST_REL
      (\left_value raw_row.
         LIST_REL
           (\right_value raw.
              registered_case10173_raw_product_relation
                left_value right_value raw)
           right raw_row)
      left historical_left_outer /\
  LIST_REL
      (\right_value raw_row.
         LIST_REL
           (\left_value raw.
              registered_case10173_raw_product_relation
                right_value left_value raw)
           left raw_row)
      right historical_right_outer ==>
  registered_case10173_raw_outer_matrices_aligned
    compact_left_rows compact_right_rows
    historical_left_outer historical_right_outer
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> metis_tac [registered_case10173_raw_outer_source_rows_aligned]
QED

Theorem registered_case10173_bounded_hessian64_rows_every:
  bounded_hessian64_rows values = SOME rows /\ EVERY property values ==>
  EVERY (EVERY property) rows
Proof
  rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_equal_width_matrices_list_rel:
  !left right.
    LENGTH left = LENGTH right /\
    EVERY (\row. LENGTH row = width) left /\
    EVERY (\row. LENGTH row = width) right ==>
    LIST_REL (\left_row right_row.
      LENGTH left_row = LENGTH right_row) left right
Proof
  Induct
  >> Cases_on `right`
  >> rw [LIST_REL_def]
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_raw_matrix_add_object_trace:
  EVERY (EVERY registered_case10173_raw_interval_object) left /\
  EVERY (EVERY registered_case10173_raw_interval_object) right /\
  LIST_REL (\left_row right_row.
    LENGTH left_row = LENGTH right_row) left right ==>
  ?result.
    registered_case10173_fs_raw_interval_matrix_add_object
      left right = SOME result /\
    registered_case10173_raw_matrices_add left right result /\
    EVERY (EVERY registered_case10173_raw_interval_object) result
Proof
  strip_tac
  >> mp_tac
       (Q.SPECL [`left`,`right`]
          registered_case10173_raw_matrix_add_objects)
  >> impl_tac >- simp []
  >> disch_then (qx_choose_then `result` strip_assume_tac)
  >> qexists_tac `result`
  >> imp_res_tac registered_case10173_raw_matrix_add_from_relation
  >> simp []
QED

Theorem registered_case10173_raw_outer_typed_shape6:
  LENGTH left = 6 /\ LENGTH right = 6 /\
  registered_case10173_fs_raw_interval_outer_object
      (MAP bounded_interval64_object_cv left)
      (MAP bounded_interval64_object_cv right) = SOME raw_rows ==>
  LENGTH raw_rows = 6 /\ EVERY (\row. LENGTH row = 6) raw_rows
Proof
  strip_tac
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_shape
  >> gvs [EVERY_MAP]
QED

val _ = export_theory ();
