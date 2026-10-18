(*****************************************************************************
 * Packet-independent refinement for the registered historical first-order
 * dihedral evaluator.
 *
 * The source computes a dead local delta value with its literal association,
 * while the decimal checker uses a tighter fused value for the supplied root
 * certificate.  It also groups the source delta gradient differently from
 * the fast decimal implementation.  The packet contract therefore supplies
 * successful source-value evaluation and exact equality between the source
 * and fast gradients.  This theorem composes those facts with the successful
 * typed first-order calculation for an arbitrary authenticated packet.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalFirstOrderGeneralEval
Ancestors
  compute_registeredCase10173HistoricalSourceDeltaGeneralEval
  compute_registeredCase10173HistoricalUGeneralEval
  compute_registeredCase10173HistoricalSecondOrderBoxEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_historical_first_order_general_eval:
  bounded_source_delta64_value_decimal [x0;x1;x2;x3;x4;x5] =
      SOME source_delta /\
  bounded_source_delta64_gradient_decimal [x0;x1;x2;x3;x4;x5] =
      SOME source_gradient /\
  bounded_delta64_pair_products_decimal [x0;x1;x2;x3;x4;x5] =
      SOME source_products /\
  bounded_delta64_gradient_from_products source_products =
      SOME source_gradient /\
  bounded_historical_dihedral_first64_decimal [x0;x1;x2;x3;x4;x5]
      root_delta root_four_x0
      [root_derivative;root_four_reciprocal;u_reciprocal;
       special_root_reciprocal;b_reciprocal] =
      SOME (value,gradient) /\
  200 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_first_order»
        [from_cv
           (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5]);
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv root_four_x0)])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (bounded_interval64_object_cv value)
          (bounded_interval64_object_cv_list gradient))),refs)
Proof
  rpt strip_tac
  >> qpat_x_assum
       `bounded_historical_dihedral_first64_decimal _ _ _ _ = SOME _`
       (fn th => assume_tac th >> mp_tac th)
  >> disch_then
       (mp_tac o MATCH_MP
         compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace)
  >> strip_tac
  >> gvs []
  >> `LENGTH delta_gradient = 6` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_delta64_gradient_from_products_length]
  >> `LENGTH root_gradient = 6` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_scale_decimal_length]
  >> `LENGTH delta_x4_gradient = 6` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_delta_x4_gradient_length]
  >> `LENGTH b_gradient_base = 6` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_scale_decimal_length]
  >> `LENGTH b_gradient = 6` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_interval64_list_add_at_length]
  >> `LENGTH c = 6` by
       metis_tac
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.bounded_historical_c_vector_decimal_lengths]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalFirstOrderEvalTheory.registered_case10173_fs_hist_first_order_composition_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (qexists_tac `bounded_interval64_object_cv source_delta`
      >> irule
        compute_registeredCase10173HistoricalSourceDeltaGeneralEvalTheory.registered_case10173_source_delta64_value_decimal_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> qexists_tac `bounded_interval64_object_cv b`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient`
  >> qexists_tac `bounded_interval64_object_cv_list b_gradient_base`
  >> qexists_tac `bounded_interval64_object_cv_list c`
  >> qexists_tac `bounded_interval64_object_cv_list delta_gradient`
  >> qexists_tac `bounded_interval64_object_cv_list delta_x4_gradient`
  >> qexists_tac `bounded_interval64_object_cv delta_x4`
  >> qexists_tac `bounded_interval64_object_cv_list gradient_base`
  >> qexists_tac `bounded_interval64_object_cv quotient`
  >> qexists_tac `bounded_interval64_object_cv u_reciprocal`
  >> qexists_tac `bounded_interval64_object_cv root_derivative`
  >> qexists_tac `bounded_interval64_object_cv_list root_gradient`
  >> qexists_tac `bounded_interval64_object_cv special_gradient`
  >> qexists_tac `bounded_interval64_object_cv two_over_root_four`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u126)
          (bounded_interval64_object_cv_list u126_gradient)`
  >> qexists_tac
       `Pair (bounded_interval64_object_cv u135)
          (bounded_interval64_object_cv_list u135_gradient)`
  >> rpt conj_tac
  >- (irule
        compute_registeredCase10173HistoricalUGeneralEvalTheory.registered_case10173_historical_u126_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalUGeneralEvalTheory.registered_case10173_historical_u135_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_final_value_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_positive_inv_after_scale2_eval
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `twice_root_delta`
      >> simp
           [compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_interval_scale_two_object_typed_exact])
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSourceDeltaGeneralEvalTheory.registered_case10173_source_delta64_gradient_decimal_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4GeneralEvalTheory.registered_case10173_historical_delta_x4_value_environment_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_interval_mul_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_list_scale_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_fs_hist_replace_three_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_c_vector_six_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_special_gradient_general_typed_eval
      >> simp []
      >> qexists_tac `special_root_reciprocal`
      >> simp [])
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
  >- (irule
        compute_registeredCase10173HistoricalDeltaX4SecondEvalTheory.registered_case10173_fs_hist_delta_x4_gradient_list_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_two_over_root_four_general_typed_eval
      >> simp []
      >> qexists_tac `root_four_reciprocal`
      >> simp []
      >> qexists_tac `two`
      >> simp [])
  >- (ho_match_mp_tac
        compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_quotient_typed_eval
      >> qexists_tac `b_reciprocal`
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_reciprocal_u_general_typed_eval
  >> simp []
  >> qexists_tac `u_product`
  >> simp []
QED

val _ = export_theory ();
