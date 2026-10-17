(*****************************************************************************
 * Exact registered delta value and gradient calculations at the genuine
 * historical case-10173 center.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalDeltaCenterEval
Ancestors
  compute_registeredCase10173HistoricalUCenterEval
  compute_registeredCase10173HistoricalDeltaValueEval
  compute_registeredCase10173HistoricalDeltaGradientEval
Libs
  bossLib preamble wordsLib

Theorem registered_case10173_historical_center_delta_value_local_object:
  ?value.
    registered_case10173_fs_angle_delta_value_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 = SOME value
Proof
  simp
    [registered_case10173_historical_center_x0_def,
     registered_case10173_historical_center_x1_def,
     registered_case10173_historical_center_x2_def,
     registered_case10173_historical_center_x3_def,
     registered_case10173_historical_center_x4_def,
     registered_case10173_historical_center_x5_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_center_delta_gradient_local_object:
  ?g0 g1 g2 g3 g4 g5.
    registered_case10173_fs_angle_delta_gradient_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 =
    SOME (registered_case10173_cv_list [g0;g1;g2;g3;g4;g5])
Proof
  simp
    [registered_case10173_historical_center_x0_def,
     registered_case10173_historical_center_x1_def,
     registered_case10173_historical_center_x2_def,
     registered_case10173_historical_center_x3_def,
     registered_case10173_historical_center_x4_def,
     registered_case10173_historical_center_x5_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_center_delta_value_eval:
  registered_case10173_fs_angle_delta_value_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 = SOME value /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_value»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv value),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalDeltaValueEvalTheory.registered_case10173_fs_angle_delta_value_object_eval
  >> simp []
QED

Theorem registered_case10173_historical_center_delta_gradient_eval:
  registered_case10173_fs_angle_delta_gradient_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x3
      registered_case10173_historical_center_x4
      registered_case10173_historical_center_x5 = SOME gradient /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_delta_gradient»
        [from_cv registered_case10173_historical_center_environment_object])
      (refs:hol_refs) = (M_success (from_cv gradient),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_historical_center_environment_object_def]
  >> irule
       compute_registeredCase10173HistoricalDeltaGradientEvalTheory.registered_case10173_fs_angle_delta_gradient_object_eval
  >> simp []
QED

val _ = export_theory ();
