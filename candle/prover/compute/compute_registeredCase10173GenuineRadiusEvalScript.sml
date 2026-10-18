(*****************************************************************************
 * Exact registered radius preparation for the authenticated first
 * case-10173 job.
 *
 * The source program derives rational radii from the original source box and
 * then rounds them upward to the 10^12 fixed scale.  The fast decimal packet
 * carries the same six fixed radii.  This theory proves that equality from
 * the literal registered computation; it does not trust a copied radius
 * fixture.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineRadiusEval
Ancestors
  compute_registeredCase10173RootRecordValue
  compute_registeredCase10173RadiiEval
  compute_registeredCase10173HistItemCompleteObjectEval
  compute_boundedCase10173HistoricalCellDecimalData
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_historical_radii_words_def:
  registered_case10173_historical_radii_words =
    case bounded_case10173_decimal_packet0_source_aligned of
    | BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta
        center_root_four_x0 center_reciprocals box_root_delta
        box_root_four_x0 box_reciprocals => radii
End

Definition registered_case10173_historical_encoded_radii_def:
  registered_case10173_historical_encoded_radii =
    MAP
      (\value.
        (bounded_word64_object_cv value,
         Num 999999999999))
      registered_case10173_historical_radii_words
End

val registered_case10173_genuine_radius_pure_eval =
  time cv_eval
    ``compute_eval_pure 1000
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_q_fixed_list_round_upper»
          [App «candle_cv_q_radius_list»
            [from_cv registered_case10173_first_job_boxes]])``;

val _ = save_thm
  ("registered_case10173_genuine_radius_pure_eval",
   registered_case10173_genuine_radius_pure_eval);

Theorem registered_case10173_genuine_radius_pure_eval_value:
  compute_eval_pure 1000
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list»
          [from_cv registered_case10173_first_job_boxes]]) =
    SOME
      (from_cv
        (registered_case10173_q_cv_list
          registered_case10173_historical_encoded_radii))
Proof
  simp
    [registered_case10173_genuine_radius_pure_eval,
     registered_case10173_historical_encoded_radii_def,
     registered_case10173_historical_radii_words_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     registered_case10173_q_cv_list_def,
     compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_def,
     compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_genuine_radius_eval:
  1000 <= clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list»
          [from_cv registered_case10173_first_job_boxes]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_q_cv_list
          registered_case10173_historical_encoded_radii)),refs)
Proof
  strip_tac
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `1000`
  >> simp [registered_case10173_genuine_radius_pure_eval_value]
QED

Theorem registered_case10173_historical_encoded_radii_numerators:
  registered_case10173_q_numerator_cv_list
      registered_case10173_historical_encoded_radii =
    registered_case10173_word64_object_cv_list
      registered_case10173_historical_radii_words
Proof
  rw
    [registered_case10173_historical_encoded_radii_def,
     registered_case10173_historical_radii_words_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def,
     registered_case10173_q_numerator_cv_list_def,
     compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_word64_object_cv_list_def]
  >> simp
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_def]
QED

val _ = export_theory ();
