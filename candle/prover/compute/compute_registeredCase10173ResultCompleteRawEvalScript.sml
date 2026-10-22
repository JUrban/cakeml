(*****************************************************************************
 * Registered evaluator semantics for the historical raw Taylor completion.
 *
 * Polynomial multiplication deliberately accumulates integer products before
 * rounding the center value, center gradient, and Hessian exactly once.  This
 * layer authenticates that literal source boundary and then reuses the proved
 * rounded Taylor completion theorem.
 *****************************************************************************)
Theory compute_registeredCase10173ResultCompleteRawEval
Ancestors
  compute_registeredCase10173HistoricalRawOuterEval
  compute_registeredCase10173TaylorCompleteObjectEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_complete_raw_body_def:
  registered_case10173_fs_result_complete_raw_body =
    App «candle_cv_fs_result_complete_rounded»
      [Var «radii»;
       Var «domain»;
       App «candle_cv_fs_first_make»
         [App «candle_cv_fs_raw_interval_round»
            [App «candle_cv_fs_scale» [];
             App «candle_cv_fs_first_value» [Var «raw_center»]];
          App «candle_cv_fs_raw_interval_list_round»
            [App «candle_cv_fs_scale» [];
             App «candle_cv_fs_first_gradient» [Var «raw_center»]]];
       App «candle_cv_fs_raw_interval_matrix_round»
         [App «candle_cv_fs_scale» [];Var «raw_hessian»]]
End

Theorem registered_case10173_fs_result_complete_raw_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_complete_raw» =
    SOME
      ([«radii»;«domain»;«raw_center»;«raw_hessian»],
       registered_case10173_fs_result_complete_raw_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_complete_raw_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_raw»
        [from_cv radii;from_cv result_domain_cv;
         from_cv (Pair raw_center_value
           (registered_case10173_cv_list raw_center_gradient));
         from_cv (registered_case10173_cv_matrix raw_hessian)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);
         («domain»,from_cv result_domain_cv);
         («raw_center»,
          from_cv (Pair raw_center_value
            (registered_case10173_cv_list raw_center_gradient)));
         («raw_hessian»,
          from_cv (registered_case10173_cv_matrix raw_hessian))]
        registered_case10173_fs_result_complete_raw_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_result_complete_raw_lookup]
QED

Theorem registered_case10173_fs_raw_interval_round_scale_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw =
      SOME rounded /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_round»
        [App «candle_cv_fs_scale» [];from_cv raw])
      (refs:hol_refs) =
    (M_success (from_cv rounded),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_round»
            [from_cv (Num 1000000000000);from_cv raw]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_interval_list_round_scale_eval:
  registered_case10173_fs_raw_interval_list_round_object
      1000000000000 raw = SOME rounded /\
  LENGTH raw + 11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_round»
        [App «candle_cv_fs_scale» [];
         from_cv (registered_case10173_cv_list raw)])
      (refs:hol_refs) =
    (M_success (from_cv (registered_case10173_cv_list rounded)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_round»
            [from_cv (Num 1000000000000);
             from_cv (registered_case10173_cv_list raw)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_interval_matrix_round_scale_eval:
  registered_case10173_fs_raw_interval_matrix_round_object
      1000000000000 raw = SOME rounded /\
  SUM (MAP LENGTH raw) + LENGTH raw + 11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_round»
        [App «candle_cv_fs_scale» [];
         from_cv (registered_case10173_cv_matrix raw)])
      (refs:hol_refs) =
    (M_success (from_cv (registered_case10173_cv_matrix rounded)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_matrix_round»
            [from_cv (Num 1000000000000);
             from_cv (registered_case10173_cv_matrix raw)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_raw_interval_matrix_round_object_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_first_round_scale_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw_value =
      SOME (bounded_interval64_object_cv center_value) /\
  registered_case10173_fs_raw_interval_list_round_object
      1000000000000 raw_gradient =
      SOME (MAP bounded_interval64_object_cv center_gradient) /\
  LENGTH raw_gradient + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [App «candle_cv_fs_raw_interval_round»
           [App «candle_cv_fs_scale» [];from_cv raw_value];
         App «candle_cv_fs_raw_interval_list_round»
           [App «candle_cv_fs_scale» [];
            from_cv (registered_case10173_cv_list raw_gradient)]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv_list center_gradient))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv (bounded_interval64_object_cv center_value);
             from_cv
               (bounded_interval64_object_cv_list center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule registered_case10173_fs_raw_interval_round_scale_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule EQ_TRANS
      >> qexists_tac
           `(M_success
             (from_cv
               (registered_case10173_cv_list
                 (MAP bounded_interval64_object_cv center_gradient))),refs)`
      >> conj_tac
      >- (irule registered_case10173_fs_raw_interval_list_round_scale_eval
          >> simp [])
      >> simp
           [compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv])
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_raw_interval_round_scale_first_value_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw_value =
      SOME rounded /\
  11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_round»
        [App «candle_cv_fs_scale» [];
         App «candle_cv_fs_first_value»
           [from_cv (Pair raw_value raw_gradient)]])
      (refs:hol_refs) =
    (M_success (from_cv rounded),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_round»
            [from_cv (Num 1000000000000);from_cv raw_value]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_value_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_interval_list_round_scale_first_gradient_eval:
  registered_case10173_fs_raw_interval_list_round_object
      1000000000000 raw_gradient = SOME rounded /\
  LENGTH raw_gradient + 11 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_list_round»
        [App «candle_cv_fs_scale» [];
         App «candle_cv_fs_first_gradient»
           [from_cv (Pair raw_value
             (registered_case10173_cv_list raw_gradient))]])
      (refs:hol_refs) =
    (M_success (from_cv (registered_case10173_cv_list rounded)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_round»
            [from_cv (Num 1000000000000);
             from_cv (registered_case10173_cv_list raw_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval,
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_first_gradient_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_eval
  >> simp []
QED

Theorem registered_case10173_fs_raw_first_round_scale_source_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw_value =
      SOME (bounded_interval64_object_cv center_value) /\
  registered_case10173_fs_raw_interval_list_round_object
      1000000000000 raw_gradient =
      SOME (MAP bounded_interval64_object_cv center_gradient) /\
  LENGTH raw_gradient + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_first_make»
        [App «candle_cv_fs_raw_interval_round»
           [App «candle_cv_fs_scale» [];
            App «candle_cv_fs_first_value»
              [from_cv (Pair raw_value
                (registered_case10173_cv_list raw_gradient))]];
         App «candle_cv_fs_raw_interval_list_round»
           [App «candle_cv_fs_scale» [];
            App «candle_cv_fs_first_gradient»
              [from_cv (Pair raw_value
                (registered_case10173_cv_list raw_gradient))]]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv center_value)
          (bounded_interval64_object_cv_list center_gradient))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_first_make»
            [from_cv (bounded_interval64_object_cv center_value);
             from_cv
               (bounded_interval64_object_cv_list center_gradient)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            registered_case10173_fs_raw_interval_round_scale_first_value_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule EQ_TRANS
      >> qexists_tac
           `(M_success
             (from_cv
               (registered_case10173_cv_list
                 (MAP bounded_interval64_object_cv center_gradient))),refs)`
      >> conj_tac
      >- (irule
            registered_case10173_fs_raw_interval_list_round_scale_first_gradient_eval
          >> simp [])
      >> simp
           [compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv])
  >> irule
       compute_registeredCase10173HistoricalBasicEvalTheory.registered_case10173_fs_first_make_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_result_complete_raw_object_eval:
  bounded_object_fs_raw_interval_round 1000000000000 raw_center_value =
      SOME (bounded_interval64_object_cv center_value) /\
  registered_case10173_fs_raw_interval_list_round_object
      1000000000000 raw_center_gradient =
      SOME (MAP bounded_interval64_object_cv center_gradient) /\
  registered_case10173_fs_raw_interval_matrix_round_object
      1000000000000 raw_hessian =
      SOME (MAP (MAP bounded_interval64_object_cv) hessian_rows) /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_object_fs_taylor_complete radii result_domain center_value
      center_gradient hessian hessian_rows = SOME result /\
  LENGTH raw_center_gradient + 13 < clock /\
  SUM (MAP LENGTH raw_hessian) + LENGTH raw_hessian + 13 < clock /\
  256 *
      (2 * LENGTH radii + LENGTH hessian_rows +
       LENGTH center_gradient + 2) + 1 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_raw»
        [from_cv
           (registered_case10173_word64_object_cv_list radii);
         from_cv (bounded_bool_object_cv result_domain);
         from_cv
           (Pair raw_center_value
             (registered_case10173_cv_list raw_center_gradient));
         from_cv (registered_case10173_cv_matrix raw_hessian)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  strip_tac
  >> rw [registered_case10173_fs_result_complete_raw_unfold]
  >> simp
       [registered_case10173_fs_result_complete_raw_body_def,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_complete_rounded»
            [from_cv
               (registered_case10173_word64_object_cv_list radii);
             from_cv (bounded_bool_object_cv result_domain);
             from_cv
               (Pair (bounded_interval64_object_cv center_value)
                 (bounded_interval64_object_cv_list center_gradient));
             from_cv
               (bounded_interval64_object_cv_matrix hessian_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac >- irule compute_execProofTheory.compute_eval_from_cv
      >> conj_tac >- irule compute_execProofTheory.compute_eval_from_cv
      >> conj_tac
      >- (simp_tac std_ss [compute_execTheory.from_cv_def]
          >> irule
               (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                 registered_case10173_fs_raw_first_round_scale_source_eval)
          >> simp []
          >> intLib.ARITH_TAC)
      >> rw
           [GSYM compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_cv_matrix_map_bounded_interval64_object_cv]
      >> irule registered_case10173_fs_raw_interval_matrix_round_scale_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173TaylorCompleteObjectEvalTheory.registered_case10173_fs_result_complete_rounded_object_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `hessian`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
