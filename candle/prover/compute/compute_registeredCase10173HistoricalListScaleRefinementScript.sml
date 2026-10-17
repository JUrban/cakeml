(*****************************************************************************
 * Connect the registered two-stage list scaler to the typed bounded object
 * calculation used by the historical first- and second-order refinements.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalListScaleRefinement
Ancestors
  compute_registeredCase10173HistoricalListArithmeticEval
Libs
  bossLib preamble

Theorem registered_case10173_cv_list_map_bounded_interval64_object_cv:
  !values.
    registered_case10173_cv_list
      (MAP bounded_interval64_object_cv values) =
    bounded_interval64_object_cv_list values
Proof
  Induct
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Theorem registered_case10173_fsn_interval_list_scale_object_bounded:
  !scalar values object_result.
    bounded_object_fs_interval_list_scale_decimal scalar values =
      SOME object_result ==>
    ?scaled_values.
      registered_case10173_fsn_interval_list_scale_object
        (bounded_interval64_object_cv scalar)
        (MAP bounded_interval64_object_cv values) = SOME scaled_values /\
      registered_case10173_cv_list scaled_values = object_result
Proof
  Induct_on `values`
  >- (rw
        [compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_def]
      >> qexists_tac `[]`
      >> simp
           [registered_case10173_fsn_interval_list_scale_object_def,
            registered_case10173_fs_raw_interval_list_scale_object_def,
            registered_case10173_fs_raw_interval_list_round_object_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def])
  >> rpt strip_tac
  >> Cases_on
       `bounded_object_fs_raw_interval_mul
          (bounded_interval64_object_cv scalar)
          (bounded_interval64_object_cv h)`
  >> gvs
       [compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_def]
  >> Cases_on `bounded_object_fs_raw_interval_round 1000000000000 x`
  >> gvs
       [compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_def,
        compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_def]
  >> Cases_on `bounded_object_fs_interval_list_scale_decimal scalar values`
  >> gvs
       [compute_boundedObjectTaylorProductDecimalTheory.bounded_object_fs_interval_list_scale_decimal_def]
  >> first_x_assum drule
  >> strip_tac
  >> gvs [registered_case10173_fsn_interval_list_scale_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_scale_object
          (bounded_interval64_object_cv scalar)
          (MAP bounded_interval64_object_cv values)`
  >> gvs []
  >> qexists_tac `x'::scaled_values`
  >> simp
       [registered_case10173_fsn_interval_list_scale_object_def,
        registered_case10173_fs_raw_interval_list_scale_object_def,
        registered_case10173_fs_raw_interval_list_round_object_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Theorem registered_case10173_fsn_interval_list_scale_bounded_eval:
  bounded_object_fs_interval_list_scale_decimal scalar values =
      SOME (bounded_interval64_object_cv_list scaled_values) /\
  LENGTH values + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_interval_list_scale»
        [from_cv (bounded_interval64_object_cv scalar);
         from_cv (bounded_interval64_object_cv_list values)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_list scaled_values)),refs)
Proof
  strip_tac
  >> drule registered_case10173_fsn_interval_list_scale_object_bounded
  >> disch_then (qx_choose_then `object_values` strip_assume_tac)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fsn_interval_list_scale»
          [from_cv (bounded_interval64_object_cv scalar);
           from_cv
             (registered_case10173_cv_list
               (MAP bounded_interval64_object_cv values))]) refs =
      (M_success
        (from_cv (registered_case10173_cv_list object_values)),refs)` by
       (irule registered_case10173_fsn_interval_list_scale_object_eval
        >> simp [])
  >> gvs
       [registered_case10173_cv_list_map_bounded_interval64_object_cv]
QED

val _ = export_theory ();
