(*****************************************************************************
 * Registered source refinement for the supplied historical square-root jet.
 *
 * This connects the compact 21-entry typed Hessian calculation to the native
 * full six-by-six matrix returned by the literal Flyspeck source.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSqrtSecondEval
Ancestors
  compute_registeredCase10173HistoricalSqrtHessianEval
  compute_registeredCase10173HistoricalListScaleRefinement
Libs
  bossLib preamble intLib

Theorem registered_case10173_raw_scale_two_endpoint_exact:
  bounded_signed64_normalized value /\
  bounded_signed64_add value value = SOME target ==>
  bounded_object_fs_raw_scale 2 (bounded_signed64_object_cv value) =
    SOME (bounded_signed64_object_cv target)
Proof
  rpt strip_tac
  >> Cases_on `value`
  >> rename1 `BoundedSigned64 negative magnitude`
  >> Cases_on `negative`
  >> simp
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_raw_scale_def,
        compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> imp_res_tac
       compute_boundedSignedEndpointAddTheory.bounded_signed64_add_value
  >> Cases_on `target`
  >> rename1 `BoundedSigned64 target_negative target_magnitude`
  >> Cases_on `target_negative`
  >> fs
       [compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_to_int_def,
        compute_boundedSignedEndpointTheory.bounded_signed64_normalized_def,
        integerTheory.INT_OF_NUM_EQ]
  >> TRY
       (irule (iffLR integerTheory.INT_OF_NUM_EQ)
        >> simp [integerTheory.INT_OF_NUM_MUL]
        >> intLib.ARITH_TAC)
  >> TRY
       (`0 < w2n target_magnitude` by
          simp
            [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
             wordsTheory.w2n_eq_0]
        >> intLib.ARITH_TAC)
  >> TRY
       (`0 < w2n magnitude` by
          simp
            [GSYM arithmeticTheory.NOT_ZERO_LT_ZERO,
             wordsTheory.w2n_eq_0]
        >> intLib.ARITH_TAC)
QED

Theorem registered_case10173_interval_scale_two_object_typed_exact:
  bounded_historical_scale2 input = SOME twice ==>
  registered_case10173_fs_interval_raw_scale_object 2
      (bounded_interval64_object_cv input) =
    SOME (bounded_interval64_object_cv twice)
Proof
  Cases_on `input`
  >> Cases_on `twice`
  >> simp
       [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def,
        compute_boundedIntervalAddTheory.bounded_interval64_add_def,
        compute_boundedIntervalAddTheory.bounded_interval64_add_unchecked_def,
        compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_interval_raw_scale_object_def,
        compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def]
  >> every_case_tac
  >> gvs [compute_boundedIntervalTheory.bounded_interval64_valid_def]
  >> imp_res_tac registered_case10173_raw_scale_two_endpoint_exact
  >> gvs []
QED

Definition registered_case10173_fs_hist_second_value_body_def:
  registered_case10173_fs_hist_second_value_body =
    Uop Fst (Var «second»)
End

Theorem registered_case10173_fs_hist_second_value_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_value» =
    SOME ([«second»],registered_case10173_fs_hist_second_value_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_second_value_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_value»
        [from_cv
          (Pair (value:cv) (Pair (gradient:cv) (hessian:cv)) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv value),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_second_value_lookup,
        registered_case10173_fs_hist_second_value_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_negative_inv_after_scale2_eval:
  bounded_historical_scale2 input = SOME twice /\
  bounded_interval64_positive_inv_certificate_decimal twice reciprocal /\
  15 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_hist_positive_inv»
          [App «candle_cv_fs_angle_interval_scale»
            [Num 2;from_cv (bounded_interval64_object_cv input)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_interval64_object_cv
          (bounded_interval64_neg reciprocal))),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg»
            [from_cv (bounded_interval64_object_cv reciprocal)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_positive_inv_after_scale2_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `twice`
      >> simp [registered_case10173_interval_scale_two_object_typed_exact])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Definition registered_case10173_fs_hist_second_sqrt_supplied_body_def:
  registered_case10173_fs_hist_second_sqrt_supplied_body =
    Let «input_value»
      (App «candle_cv_fs_hist_second_value» [Var «input»])
      (Let «input_gradient»
        (App «candle_cv_fs_hist_second_gradient» [Var «input»])
        (Let «input_hessian»
          (App «candle_cv_fs_hist_second_hessian» [Var «input»])
          (Let «derivative_value»
            (App «candle_cv_fs_hist_positive_inv»
              [App «candle_cv_fs_angle_interval_scale»
                [Num 2;Var «root_value»]])
            (Let «logarithmic_derivative»
              (App «candle_cv_fs_interval_neg»
                [App «candle_cv_fs_hist_positive_inv»
                  [App «candle_cv_fs_angle_interval_scale»
                    [Num 2;Var «input_value»]]])
              (App «candle_cv_fs_hist_second_make»
                [Var «root_value»;
                 App «candle_cv_fsn_interval_list_scale»
                   [Var «derivative_value»;Var «input_gradient»];
                 App «candle_cv_fs_hist_sqrt_hessian»
                   [Var «derivative_value»;Var «logarithmic_derivative»;
                    Var «input_gradient»;Var «input_hessian»]])))))
End

Theorem registered_case10173_fs_hist_second_sqrt_supplied_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_second_sqrt_supplied» =
    SOME
      ([«input»;«root_value»],
       registered_case10173_fs_hist_second_sqrt_supplied_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_second_sqrt_supplied_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_sqrt_supplied»
        [from_cv input;from_cv root_value]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«input»,from_cv input);(«root_value»,from_cv root_value)]
        registered_case10173_fs_hist_second_sqrt_supplied_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_hist_second_sqrt_supplied_lookup]
QED

Theorem registered_case10173_fs_hist_second_sqrt_supplied_trace_typed_eval:
  LENGTH gradient = 6 /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_historical_scale2 root = SOME twice_root /\
  bounded_interval64_positive_inv_certificate_decimal
    twice_root derivative /\
  bounded_historical_scale2 value = SOME twice_value /\
  bounded_interval64_positive_inv_certificate_decimal
    twice_value logarithmic_reciprocal /\
  bounded_interval64_list_scale_decimal derivative gradient =
    SOME result_gradient /\
  bounded_historical_sqrt_hessian_decimal derivative
    (bounded_interval64_neg logarithmic_reciprocal) gradient
    bounded_delta64_hessian_indices hessian = SOME result_hessian /\
  bounded_hessian64_rows result_hessian = SOME result_rows /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_sqrt_supplied»
        [from_cv
          (Pair
            (bounded_interval64_object_cv value)
            (Pair
              (bounded_interval64_object_cv_list gradient)
              (bounded_interval64_object_cv_matrix hessian_rows)));
         from_cv (bounded_interval64_object_cv root)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv root)
          (Pair
            (bounded_interval64_object_cv_list result_gradient)
            (bounded_interval64_object_cv_matrix result_rows)))),refs)
Proof
  rpt strip_tac
  >> `registered_case10173_sqrt_hessian_rows_decimal derivative
        (bounded_interval64_neg logarithmic_reciprocal) gradient
        hessian_rows = SOME result_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSqrtHessianEvalTheory.registered_case10173_sqrt_hessian_rows_decimal_compact]
  >> `LENGTH hessian_rows = 6 /\
      EVERY (\row. LENGTH row = 6) hessian_rows` by
       (qpat_x_assum
          `bounded_hessian64_rows hessian = SOME hessian_rows`
          (fn th => mp_tac th)
        >> rw [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
        >> every_case_tac
        >> gvs [])
  >> rw [registered_case10173_fs_hist_second_sqrt_supplied_unfold]
  >> simp
       [registered_case10173_fs_hist_second_sqrt_supplied_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv value)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_second_value_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv_list gradient)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_gradient_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv_matrix hessian_rows)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv derivative)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_positive_inv_after_scale2_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `twice_root`
      >> simp [registered_case10173_interval_scale_two_object_typed_exact])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv
            (bounded_interval64_neg logarithmic_reciprocal))`
  >> conj_tac
  >- (irule registered_case10173_fs_hist_negative_inv_after_scale2_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 6)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_second_make»
            [from_cv (bounded_interval64_object_cv root);
             from_cv (bounded_interval64_object_cv_list result_gradient);
             from_cv (bounded_interval64_object_cv_matrix result_rows)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> conj_tac
      >- (irule
            compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalSqrtHessianEvalTheory.registered_case10173_fs_hist_sqrt_hessian_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_make_eval)
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_second_sqrt_supplied_typed_eval:
  LENGTH gradient = 6 /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  bounded_historical_sqrt_second_decimal value gradient hessian root
      derivative logarithmic_reciprocal =
    SOME (result_root,result_gradient,result_hessian) /\
  bounded_hessian64_rows result_hessian = SOME result_rows /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_sqrt_supplied»
        [from_cv
          (Pair
            (bounded_interval64_object_cv value)
            (Pair
              (bounded_interval64_object_cv_list gradient)
              (bounded_interval64_object_cv_matrix hessian_rows)));
         from_cv (bounded_interval64_object_cv root)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (bounded_interval64_object_cv result_root)
          (Pair
            (bounded_interval64_object_cv_list result_gradient)
            (bounded_interval64_object_cv_matrix result_rows)))),refs)
Proof
  rpt strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_sqrt_second_decimal_source_trace
  >> strip_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_second_sqrt_supplied_trace_typed_eval)
  >> simp []
  >> qexists_tac `derivative`
  >> qexists_tac `hessian`
  >> qexists_tac `logarithmic_reciprocal`
  >> qexists_tac `result_hessian`
  >> simp []
QED

val _ = export_theory ();
