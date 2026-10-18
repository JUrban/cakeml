(*****************************************************************************
 * Packet-independent refinement for the registered historical second-order
 * dihedral evaluator.  All numerical premises come from one successful
 * typed packet calculation; no packet constants or closed evaluator results
 * are used here.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderGeneralEval
Ancestors
  compute_registeredCase10173HistoricalFirstOrderGeneralEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_historical_second_order_general_eval:
  bounded_historical_dihedral_second64_decimal [x0;x1;x2;x3;x4;x5]
      root_delta root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) /\
  bounded_hessian64_rows hessian = SOME hessian_rows /\
  1000 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_second_order»
        [from_cv
           (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5]);
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv root_four_x0)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv value)
          (Pair (bounded_interval64_object_cv_list gradient)
            (bounded_interval64_object_cv_matrix hessian_rows)))),refs)
Proof
  rpt strip_tac
  >> qpat_x_assum
       `bounded_historical_dihedral_second64_decimal _ _ _ _ = SOME _`
       (fn th => assume_tac th >> mp_tac th)
  >> disch_then
       (mp_tac o MATCH_MP
         compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_dihedral_second64_decimal_source_trace)
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_second_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_sqrt_second_decimal_source_trace
  >> strip_tac
  >> drule
       compute_boundedObjectHistoricalSecondDecimalTheory.bounded_historical_delta_x4_second_decimal_source_trace
  >> strip_tac
  >> gvs [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def]
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalDeltaSecondEvalTheory.registered_case10173_bounded_historical_delta_gradient_box_decimal_shape
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_scale_decimal_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_delta_x4_gradient_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_add_at_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_c_vector_decimal_lengths
  >> imp_res_tac
       compute_boundedIntervalListTheory.bounded_interval64_list_add_length
  >> imp_res_tac
       compute_boundedHistoricalDihedralSecondTheory.bounded_historical_replace_three_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_u126_decimal_gradient_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_u135_decimal_gradient_length
  >> imp_res_tac
       compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_delta_x4_hessian_decimal_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_sqrt_hessian_decimal_lengths
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_b_hessian_decimal_length
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_second_hessian_decimal_lengths
  >> `LENGTH bounded_delta64_hessian_indices = 21` by EVAL_TAC
  >> `?root_hessian_rows.
        bounded_hessian64_rows root_hessian = SOME root_hessian_rows /\
        LENGTH root_hessian_rows = 6 /\
        EVERY (\row. LENGTH row = 6) root_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `?delta_x4_hessian_rows.
        bounded_hessian64_rows delta_x4_hessian =
          SOME delta_x4_hessian_rows /\
        LENGTH delta_x4_hessian_rows = 6 /\
        EVERY (\row. LENGTH row = 6) delta_x4_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `?b_hessian_base_rows.
        bounded_hessian64_rows b_hessian_base =
          SOME b_hessian_base_rows /\
        LENGTH b_hessian_base_rows = 6 /\
        EVERY (\row. LENGTH row = 6) b_hessian_base_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `?b_hessian_rows.
        bounded_hessian64_rows b_hessian = SOME b_hessian_rows /\
        LENGTH b_hessian_rows = 6 /\
        EVERY (\row. LENGTH row = 6) b_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_from_length]
  >> `bounded_interval64_matrix_scale_decimal root_four_x0
        root_hessian_rows = SOME b_hessian_base_rows` by
       metis_tac
         [compute_boundedObjectTaylorStateDecimalTheory.bounded_hessian64_rows_scale_decimal]
  >> `registered_case10173_b_hessian_rows_decimal root_delta
        two_over_root_four diagonal_reciprocal root_gradient
        b_hessian_base_rows = SOME b_hessian_rows` by
       metis_tac
         [compute_registeredCase10173HistoricalBHessianEvalTheory.registered_case10173_b_hessian_rows_decimal_compact]
  >> `registered_case10173_log_u_gradient_decimal u126_gradient
        u126_reciprocal u135_gradient u135_reciprocal =
      SOME logarithmic_u_gradient` by
       metis_tac
         [compute_registeredCase10173HistoricalLogUGradientEvalTheory.registered_case10173_log_u_gradient_decimal_compact]
  >> `LENGTH delta_x4_gradient = 6` by simp []
  >> `LENGTH b_gradient = 6` by simp []
  >> `LENGTH gradient = 6` by simp []
  >> `LENGTH logarithmic_u_gradient = 6` by simp []
  >> `bounded_hessian64_rows delta_x4_hessian =
        SOME delta_x4_hessian_rows` by simp []
  >> `bounded_hessian64_rows b_hessian = SOME b_hessian_rows` by simp []
  >> `bounded_historical_second_hessian_decimal
        (bounded_historical_extreme_interval lower_value' upper_value')
        b u_reciprocal
        delta_x4_gradient b_gradient gradient logarithmic_u_gradient
        bounded_delta64_hessian_indices delta_x4_hessian b_hessian =
      SOME hessian` by
       qpat_x_assum
         `bounded_historical_second_hessian_decimal
            (bounded_historical_extreme_interval lower_value' upper_value')
            b u_reciprocal
            delta_x4_gradient b_gradient gradient logarithmic_u_gradient
            bounded_delta64_hessian_indices delta_x4_hessian b_hessian =
          SOME hessian`
         ACCEPT_TAC
  >> `bounded_hessian64_rows hessian = SOME hessian_rows` by
       qpat_x_assum
         `bounded_hessian64_rows hessian = SOME hessian_rows`
         ACCEPT_TAC
  >> `registered_case10173_final_hessian_rows_decimal
        (bounded_historical_extreme_interval lower_value' upper_value') b
        u_reciprocal delta_x4_gradient delta_x4_hessian_rows b_gradient
        b_hessian_rows gradient logarithmic_u_gradient = SOME hessian_rows` by
       (irule
          compute_registeredCase10173HistoricalFinalHessianEvalTheory.registered_case10173_final_hessian_rows_decimal_compact
        >> simp []
        >> qexists_tac `b_hessian`
        >> qexists_tac `delta_x4_hessian`
        >> qexists_tac `hessian`
        >> simp [])
  >> `LENGTH u126_gradient = 6` by simp []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderEvalTheory.registered_case10173_fs_hist_second_order_composition_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv b`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient_base`
  >> qexists_tac `bounded_interval64_object_cv_matrix b_hessian_rows`
  >> qexists_tac `bounded_interval64_object_cv_list c`
  >> qexists_tac
       `Pair
          (bounded_interval64_object_cv
            (bounded_historical_extreme_interval lower_value upper_value))
          (Pair (bounded_interval64_object_cv_list delta_gradient)
            (bounded_interval64_object_cv_matrix derivative_rows))`
  >> qexists_tac `bounded_interval64_object_cv_list delta_x4_gradient`
  >> qexists_tac `bounded_interval64_object_cv_matrix delta_x4_hessian_rows`
  >> qexists_tac
       `Pair
          (bounded_interval64_object_cv
            (bounded_historical_extreme_interval lower_value' upper_value'))
          (Pair (bounded_interval64_object_cv_list delta_x4_gradient)
            (bounded_interval64_object_cv_matrix delta_x4_hessian_rows))`
  >> qexists_tac
       `bounded_interval64_object_cv
          (bounded_historical_extreme_interval lower_value' upper_value')`
  >> qexists_tac `bounded_interval64_object_cv_list gradient_base`
  >> qexists_tac `bounded_interval64_object_cv_list logarithmic_u_gradient`
  >> qexists_tac `bounded_interval64_object_cv quotient`
  >> qexists_tac `bounded_interval64_object_cv u_reciprocal`
  >> qexists_tac `bounded_interval64_object_cv u126_reciprocal`
  >> qexists_tac `bounded_interval64_object_cv u135_reciprocal`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv root_delta)
          (Pair (bounded_interval64_object_cv_list root_gradient)
            (bounded_interval64_object_cv_matrix root_hessian_rows))`
  >> qexists_tac `bounded_interval64_object_cv_list root_gradient`
  >> qexists_tac `bounded_interval64_object_cv_matrix root_hessian_rows`
  >> qexists_tac `bounded_interval64_object_cv special_gradient`
  >> qexists_tac `bounded_interval64_object_cv two_over_root_four`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u126)
          (bounded_interval64_object_cv_list u126_gradient)`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u135)
          (bounded_interval64_object_cv_list u135_gradient)`
  >> qexists_tac `bounded_interval64_object_cv x0`
  >> rpt conj_tac
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_final_value_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_positive_inv_pair_fst_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalUGeneralEvalTheory.registered_case10173_historical_u126_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        (SIMP_RULE std_ss
          [compute_execTheory.from_cv_def,listTheory.EL,listTheory.HD]
          (Q.SPECL
            [`0`,`[x0;x1;x2;x3;x4;x5]`,`clock - 15`,`refs`]
            compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval))
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalDeltaSecondEvalTheory.registered_case10173_fs_hist_delta_second_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_gradient_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_fs_hist_second_sqrt_supplied_typed_eval
      >> simp []
      >> qexists_tac `root_derivative`
      >> qexists_tac `delta_hessian`
      >> qexists_tac `root_logarithmic`
      >> qexists_tac `root_hessian`
      >> simp []
      >> metis_tac [])
  >- (irule
        compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_hist_replace_three_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_hist_second_gradient_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_delta_x4_second_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_c_vector_six_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFinalHessianEvalTheory.registered_case10173_fs_hist_final_hessian_rows_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fs_hist_second_hessian_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalBHessianEvalTheory.registered_case10173_fs_hist_b_hessian_typed_eval
      >> simp []
      >> conj_tac
      >- (`?r0 r1 r2 r3 r4 r5.
             root_hessian_rows = [r0;r1;r2;r3;r4;r5]` by
            metis_tac
              [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases]
          >> gvs []
          >> intLib.ARITH_TAC)
      >> qexists_tac `diagonal_reciprocal`
      >> simp [])
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_log_u_gradient_pairs_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_two_over_root_four_general_typed_eval
      >> simp []
      >> qexists_tac `root_four_reciprocal`
      >> qexists_tac `two`
      >> simp [])
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_reciprocal_u_general_typed_eval
      >> simp []
      >> qexists_tac `u_product`
      >> simp [])
  >- (irule
        compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_fs_hist_second_value_eval
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalUGeneralEvalTheory.registered_case10173_historical_u135_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_positive_inv_pair_fst_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_quotient_typed_eval
      >> qexists_tac `b_reciprocal`
      >> simp []
      >> intLib.ARITH_TAC)
  >- (ho_match_mp_tac
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_b_gradient_six_typed_eval
      >> qexists_tac `b_correction`
      >> rpt conj_tac
      >- simp []
      >- simp []
      >- (irule
            compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> irule
       (Q.INST
         [`twice_root_delta` |-> `twice_root_delta`,
          `reciprocal` |-> `special_root_reciprocal`]
         compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_special_gradient_general_typed_eval)
  >> simp []
  >> metis_tac
       [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_scale2_result_unique]
QED

val _ = export_theory ();
