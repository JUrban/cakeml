(*****************************************************************************
 * Registered evaluation of the rounded matrix wrappers used by source sqrt.
 *
 * The literal [fsn_sqrt_hessian] source uses the generic rounded matrix
 * scale and outer-product wrappers.  Their raw recursive operations already
 * have object evaluator theorems; this layer composes the final outward
 * rounding without replaying the source evaluator on a closed cell.
 *****************************************************************************)
Theory compute_registeredCase10173SqrtMatrixWrapperEval
Ancestors
  compute_registeredCase10173HistoricalRawOuterEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fsn_interval_matrix_scale_body_def:
  registered_case10173_fsn_interval_matrix_scale_body =
    App «candle_cv_fs_raw_interval_matrix_round»
      [App «candle_cv_fs_scale» [];
       App «candle_cv_fs_raw_interval_matrix_scale»
         [Var «scalar»;Var «row_lists»]]
End

Definition registered_case10173_fsn_interval_outer_body_def:
  registered_case10173_fsn_interval_outer_body =
    App «candle_cv_fs_raw_interval_matrix_round»
      [App «candle_cv_fs_scale» [];
       App «candle_cv_fs_raw_interval_outer»
         [Var «left»;Var «right»]]
End

Theorem registered_case10173_fsn_interval_matrix_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_interval_matrix_scale» =
    SOME
      ([«scalar»;«row_lists»],
       registered_case10173_fsn_interval_matrix_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_interval_outer_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fsn_interval_outer» =
    SOME
      ([«left»;«right»],registered_case10173_fsn_interval_outer_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fsn_interval_matrix_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_matrix_scale»
        [from_cv scalar;from_cv matrixvalue]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«scalar»,from_cv scalar);(«row_lists»,from_cv matrixvalue)]
        registered_case10173_fsn_interval_matrix_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fsn_interval_matrix_scale_lookup]
QED

Theorem registered_case10173_fsn_interval_outer_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_outer»
        [from_cv left;from_cv right]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«left»,from_cv left);(«right»,from_cv right)]
        registered_case10173_fsn_interval_outer_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fsn_interval_outer_lookup]
QED

Theorem registered_case10173_fsn_interval_matrix_scale_hist_equiv:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_matrix_scale»
        [from_cv scalar;from_cv matrixvalue]) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_matrix_scale»
        [from_cv scalar;from_cv matrixvalue]) refs
Proof
  strip_tac
  >> rw [registered_case10173_fsn_interval_matrix_scale_unfold]
  >> rw
       [compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_hist_matrix_scale_unfold]
  >> simp
       [registered_case10173_fsn_interval_matrix_scale_body_def,
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_hist_matrix_scale_body_def,
        compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fsn_interval_matrix_scale_typed_eval:
  bounded_interval64_matrix_scale_decimal scalar rows = SOME scaled_rows /\
  SUM (MAP LENGTH rows) + LENGTH rows + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_matrix_scale»
        [from_cv (bounded_interval64_object_cv scalar);
         from_cv (bounded_interval64_object_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix scaled_rows)),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fsn_interval_matrix_scale_hist_equiv]
  >> irule
       compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_hist_matrix_scale_typed_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fsn_interval_outer_object_eval:
  registered_case10173_fs_raw_interval_outer_object left right =
      SOME raw_rows /\
  registered_case10173_fs_raw_interval_matrix_round_object
      1000000000000 raw_rows = SOME rounded_rows /\
  LENGTH left * (LENGTH right + 1) + 5 < clock /\
  SUM (MAP LENGTH raw_rows) + LENGTH raw_rows + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_outer»
        [from_cv (registered_case10173_cv_list left);
         from_cv (registered_case10173_cv_list right)])
      (refs:hol_refs) =
    (M_success (from_cv (registered_case10173_cv_matrix rounded_rows)),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fsn_interval_outer_unfold]
  >> simp
       [registered_case10173_fsn_interval_outer_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_matrix_round»
            [from_cv (Num 1000000000000);
             from_cv (registered_case10173_cv_matrix raw_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
      >> irule
           compute_registeredCase10173HistoricalRawOuterEvalTheory.registered_case10173_fs_raw_interval_outer_object_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_round_object_eval
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
