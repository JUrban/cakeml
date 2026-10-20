(*****************************************************************************
 * Compact-to-source trace for the actual square-root Hessian.
 *
 * The decimal checker stores a symmetric six-dimensional Hessian in its 21
 * independent entries.  The unchanged source builds a full matrix for the
 * gradient outer product and only then scales and adds matrices.  This theory
 * proves that the rounded full-matrix outer product is exactly the expansion
 * of the compact self-outer calculation used by the checker.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSqrtHessianTrace
Ancestors
  compute_registeredCase10173ActualSqrtHessianEval
  compute_registeredCase10173SqrtMatrixWrapperEval
  compute_boundedObjectTaylorUnaryDecimal
Libs
  bossLib preamble intLib

Definition bounded_interval64_matrix_outer_decimal_def:
  bounded_interval64_matrix_outer_decimal [] right = SOME [] /\
  bounded_interval64_matrix_outer_decimal (left::left_rest) right =
    case bounded_interval64_list_scale_decimal left right of
    | NONE => NONE
    | SOME row =>
      case bounded_interval64_matrix_outer_decimal left_rest right of
      | NONE => NONE
      | SOME rows => SOME (row::rows)
End

Theorem registered_case10173_actual_sqrt_word_mul_div_floor_decimal_comm:
  bounded_word64_mul_div_floor_decimal left right =
    bounded_word64_mul_div_floor_decimal right left
Proof
  simp
    [compute_boundedTheory.bounded_word64_mul_div_floor_decimal_def,
     wordsTheory.WORD_MULT_COMM, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_actual_sqrt_word_mul_div_ceil_decimal_comm:
  bounded_word64_mul_div_ceil_decimal left right =
    bounded_word64_mul_div_ceil_decimal right left
Proof
  simp
    [compute_boundedTheory.bounded_word64_mul_div_ceil_decimal_def,
     wordsTheory.WORD_MULT_COMM, arithmeticTheory.MULT_COMM]
QED

Theorem registered_case10173_actual_sqrt_signed_mul_floor_decimal_comm:
  bounded_signed_word64_mul_floor_decimal left right =
    bounded_signed_word64_mul_floor_decimal right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedSignedTheory.bounded_signed_word64_mul_floor_decimal_def,
        registered_case10173_actual_sqrt_word_mul_div_floor_decimal_comm,
        registered_case10173_actual_sqrt_word_mul_div_ceil_decimal_comm,
        EQ_SYM_EQ]
QED

Theorem registered_case10173_actual_sqrt_signed_mul_ceil_decimal_comm:
  bounded_signed_word64_mul_ceil_decimal left right =
    bounded_signed_word64_mul_ceil_decimal right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedSignedTheory.bounded_signed_word64_mul_ceil_decimal_def,
        registered_case10173_actual_sqrt_word_mul_div_floor_decimal_comm,
        registered_case10173_actual_sqrt_word_mul_div_ceil_decimal_comm,
        EQ_SYM_EQ]
QED

Theorem registered_case10173_actual_sqrt_scaled_mul_floor_decimal_comm:
  bounded_scaled_mul_floor64_decimal left right =
    bounded_scaled_mul_floor64_decimal right left
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_def,
     registered_case10173_actual_sqrt_signed_mul_floor_decimal_comm]
QED

Theorem registered_case10173_actual_sqrt_scaled_mul_ceil_decimal_comm:
  bounded_scaled_mul_ceil64_decimal left right =
    bounded_scaled_mul_ceil64_decimal right left
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_scaled_mul_ceil64_decimal_def,
     registered_case10173_actual_sqrt_signed_mul_ceil_decimal_comm]
QED

Theorem registered_case10173_actual_sqrt_product_from_pairs_decimal_comm:
  bounded_interval64_product_from_pairs_decimal ll rl lu ru =
    bounded_interval64_product_from_pairs_decimal rl ll ru lu
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_interval64_product_from_pairs_decimal_def,
     registered_case10173_actual_sqrt_scaled_mul_floor_decimal_comm,
     registered_case10173_actual_sqrt_scaled_mul_ceil_decimal_comm]
QED

Theorem registered_case10173_actual_sqrt_signed64_min_comm_normalized:
  bounded_signed64_normalized left /\
  bounded_signed64_normalized right ==>
  bounded_signed64_min left right = bounded_signed64_min right left
Proof
  strip_tac
  >> Cases_on `bounded_signed64_le left right`
  >> Cases_on `bounded_signed64_le right left`
  >> fs [compute_boundedSignedEndpointTheory.bounded_signed64_min_def]
  >> metis_tac
       [compute_boundedSignedEndpointTheory.bounded_signed64_le_correct,
        compute_boundedObjectDecimalIntervalTheory.bounded_signed64_to_int_injective_normalized,
        integerTheory.INT_LE_TOTAL, integerTheory.INT_LE_ANTISYM]
QED

Theorem registered_case10173_actual_sqrt_product_mixed_decimal_comm:
  bounded_interval64_product_mixed_decimal ll lu rl ru =
    bounded_interval64_product_mixed_decimal rl ru ll lu
Proof
  simp
    [compute_boundedIntervalDecimalTheory.bounded_interval64_product_mixed_decimal_def,
     registered_case10173_actual_sqrt_scaled_mul_floor_decimal_comm,
     registered_case10173_actual_sqrt_scaled_mul_ceil_decimal_comm]
  >> Cases_on `bounded_scaled_mul_floor64_decimal ll ru`
  >> Cases_on `bounded_scaled_mul_floor64_decimal lu rl`
  >> simp []
  >> imp_res_tac
       compute_boundedIntervalDecimalTheory.bounded_scaled_mul_floor64_decimal_normalized
  >> simp [registered_case10173_actual_sqrt_signed64_min_comm_normalized]
QED

Theorem registered_case10173_actual_sqrt_interval_mul_decimal_comm:
  bounded_interval64_mul_decimal left right =
    bounded_interval64_mul_decimal right left
Proof
  Cases_on `left`
  >> Cases_on `right`
  >> simp
       [compute_boundedIntervalDecimalTheory.bounded_interval64_mul_decimal_def,
        compute_boundedIntervalDecimalTheory.bounded_interval64_mul_unchecked_decimal_def,
        registered_case10173_actual_sqrt_product_from_pairs_decimal_comm,
        registered_case10173_actual_sqrt_product_mixed_decimal_comm,
        CONJ_COMM]
  >> Cases_on `bounded_signed64_nonnegative b`
  >> Cases_on `bounded_signed64_nonpositive b0`
  >> Cases_on `bounded_signed64_nonnegative b'`
  >> Cases_on `bounded_signed64_nonpositive b0'`
  >> simp
       [registered_case10173_actual_sqrt_product_from_pairs_decimal_comm,
        registered_case10173_actual_sqrt_product_mixed_decimal_comm]
QED

Theorem registered_case10173_actual_sqrt_mul_decimal_raw_trace:
  bounded_interval64_mul_decimal left right = SOME result ==>
  ?raw_lower raw_upper.
    bounded_object_fs_raw_interval_mul
        (bounded_interval64_object_cv left)
        (bounded_interval64_object_cv right) =
      SOME (Pair raw_lower raw_upper) /\
    bounded_object_fs_raw_interval_round 1000000000000
        (Pair raw_lower raw_upper) =
      SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> drule
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> rw
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_def]
  >> every_case_tac
  >> gvs []
  >> Cases_on `x`
  >> gvs
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_raw_interval_round_def]
QED

Theorem registered_case10173_interval_list_scale_decimal_source_trace:
  !rounded.
    bounded_interval64_list_scale_decimal scalar values = SOME rounded ==>
    ?raw.
      registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv scalar)
          (MAP bounded_interval64_object_cv values) = SOME raw /\
      registered_case10173_fs_raw_interval_list_round_object
          1000000000000 raw =
        SOME (MAP bounded_interval64_object_cv rounded)
Proof
  Induct_on `values`
  >- simp
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def]
  >> rw
       [compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> imp_res_tac registered_case10173_actual_sqrt_mul_decimal_raw_trace
  >> qexists_tac `Pair raw_lower raw_upper::raw`
  >> simp
       [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_def,
        compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_def]
QED

Theorem bounded_interval64_matrix_outer_decimal_source_trace:
  !rounded_rows.
    bounded_interval64_matrix_outer_decimal left right = SOME rounded_rows ==>
    ?raw_rows.
      registered_case10173_fs_raw_interval_outer_object
          (MAP bounded_interval64_object_cv left)
          (MAP bounded_interval64_object_cv right) = SOME raw_rows /\
      registered_case10173_fs_raw_interval_matrix_round_object
          1000000000000 raw_rows =
        SOME (MAP (MAP bounded_interval64_object_cv) rounded_rows)
Proof
  Induct_on `left`
  >- simp
       [bounded_interval64_matrix_outer_decimal_def,
        compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_round_object_def]
  >> rw [bounded_interval64_matrix_outer_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac registered_case10173_interval_list_scale_decimal_source_trace
  >> res_tac
  >> qexists_tac `raw::raw_rows`
  >> simp
       [compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_round_object_def]
QED

Theorem registered_case10173_sum_every_equal:
  !lengths.
    EVERY ($= width) lengths ==>
    SUM lengths = LENGTH lengths * width
Proof
  Induct
  >> simp [arithmeticTheory.MULT_SUC]
QED

Theorem registered_case10173_fsn_interval_outer_typed_eval:
  bounded_interval64_matrix_outer_decimal left right = SOME rounded_rows /\
  LENGTH left * (LENGTH right + 1) + 5 < clock /\
  LENGTH left * LENGTH right + LENGTH left + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_outer»
        [from_cv (bounded_interval64_object_cv_list left);
         from_cv (bounded_interval64_object_cv_list right)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix rounded_rows)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_interval64_matrix_outer_decimal_source_trace
  >> imp_res_tac
       compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_shape
  >> fs []
  >> `SUM (MAP LENGTH raw_rows) = LENGTH raw_rows * LENGTH right` by
       (mp_tac
          (Q.INST [`width` |-> `LENGTH (right:bounded_interval64 list)`]
            (Q.SPEC `MAP LENGTH (raw_rows:cv list list)`
              registered_case10173_sum_every_equal))
        >> fs [])
  >> rw
       [GSYM compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv,
        GSYM compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_map_bounded_interval64_object_cv]
  >> irule
       compute_registeredCase10173SqrtMatrixWrapperEvalTheory.registered_case10173_fsn_interval_outer_object_eval
  >> conj_tac >- fs []
  >> qexists_tac `raw_rows`
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem bounded_interval64_self_outer_decimal_rows:
  LENGTH values = 6 /\
  bounded_interval64_self_outer_decimal values = SOME compact /\
  bounded_hessian64_rows compact = SOME rows ==>
  bounded_interval64_matrix_outer_decimal values values = SOME rows
Proof
  rw [listTheory.LENGTH_EQ_NUM_compute]
  >> fs
       [compute_boundedTaylorUnaryDecimalTheory.bounded_interval64_self_outer_decimal_def,
        bounded_interval64_matrix_outer_decimal_def,
        compute_boundedTaylorProductDecimalTheory.bounded_interval64_list_scale_decimal_def,
        compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> every_case_tac
  >> gvs
       [registered_case10173_actual_sqrt_interval_mul_decimal_comm]
QED

val _ = export_theory ();
