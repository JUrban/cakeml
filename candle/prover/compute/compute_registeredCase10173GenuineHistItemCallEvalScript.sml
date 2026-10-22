(*****************************************************************************
 * Lift the completed first authenticated historical item through the actual
 * registered CakeML evaluator call.  This is kept separate from the closed
 * numerical proof so evaluator-composition edits reuse that stable theory.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineHistItemCallEval
Ancestors
  compute_registeredCase10173GenuineHistItemEval
Libs
  bossLib preamble

Theorem registered_case10173_historical_center_environment_object_exact:
  registered_case10173_historical_center_environment_object =
    bounded_interval64_object_cv_list
      registered_case10173_historical_center_environment_decimal
Proof
  simp
    [compute_registeredCase10173HistoricalUCenterEvalTheory.registered_case10173_historical_center_environment_packet_exact,
     compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def]
QED

Theorem registered_case10173_historical_center_gradient_length:
  bounded_historical_dihedral_first64_decimal
      registered_case10173_historical_center_environment_decimal
      registered_case10173_historical_center_root_delta
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_reciprocals =
    SOME (value,gradient) ==>
  LENGTH gradient = 6
Proof
  strip_tac
  >> qpat_x_assum
       `bounded_historical_dihedral_first64_decimal _ _ _ _ = _`
       (fn th =>
         assume_tac
           (REWRITE_RULE
             [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_reciprocals_components]
             th))
  >> drule
       compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedHistoricalDihedralSecondTheory.bounded_historical_replace_three_length
QED

Theorem registered_case10173_genuine_historical_item_eval:
  20000 < clock ==>
  ?center_boxes result.
    registered_case10173_q_center_environment_positive
        registered_case10173_first_job_boxes = SOME center_boxes /\
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_item»
        [from_cv center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv
           (registered_case10173_q_cv_list
             registered_case10173_historical_encoded_radii);
         from_cv registered_case10173_first_job_roots])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  strip_tac
  >> mp_tac
       compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_source_inputs_exact
  >> strip_tac
  >> mp_tac
       compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_historical_item_complete
  >> strip_tac
  >> qexists_tac `center_boxes`
  >> qexists_tac `result`
  >> conj_tac >- simp []
  >> qpat_x_assum
       `registered_case10173_first_job_roots = _`
       (fn th => once_rewrite_tac [th])
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> irule
       compute_registeredCase10173HistItemCompleteObjectEvalTheory.registered_case10173_hist_item_complete_object_eval
  >> `LENGTH center_gradient = 6` by
       (irule registered_case10173_historical_center_gradient_length
        >> simp [])
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (simp
        [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_def,
         compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >> qexists_tac `registered_case10173_historical_box_environment_decimal`
  >> qexists_tac `box_gradient`
  >> qexists_tac `box_value`
  >> qexists_tac `registered_case10173_historical_center_environment_decimal`
  >> qexists_tac `center_gradient`
  >> qexists_tac `center_value`
  >> qexists_tac `hessian`
  >> qexists_tac `registered_case10173_historical_radii_words`
  >> qexists_tac `rows`
  >> rpt conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_decimal_def,
         compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- simp []
  >- (simp
        [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
         compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- simp []
  >- (simp
        [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- ACCEPT_TAC
       compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_numerators
  >- simp []
  >- simp []
  >- (once_rewrite_tac
        [GSYM registered_case10173_historical_center_environment_object_exact]
      >> mp_tac
           (Q.INST [`clock` |-> `clock - 3`]
             compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_first_order_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> qpat_x_assum
           `bounded_historical_dihedral_first64_decimal _ _ _
              registered_case10173_historical_center_reciprocals = _`
           (fn th =>
             assume_tac
               (REWRITE_RULE
                 [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_reciprocals_components]
                 th))
      >> gvs [])
  >> once_rewrite_tac
       [GSYM compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_object_exact]
  >> irule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_second_order_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
