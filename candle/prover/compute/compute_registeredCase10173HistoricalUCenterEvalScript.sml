(*****************************************************************************
 * Exact registered u126/u135 center calculations for the genuine historical
 * case-10173 packet.  The six fixed-scale interval objects below are also
 * proved to be exactly the authenticated packet's center environment.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUCenterEval
Ancestors
  compute_registeredCase10173HistoricalUObjectEmbeddingEval
  compute_registeredCase10173RootInputsBinding
Libs
  bossLib preamble wordsLib

Definition registered_case10173_historical_center_x0_def:
  registered_case10173_historical_center_x0 =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F 4802337500000w)
        (BoundedSigned64 F 4802337500001w))
End

Definition registered_case10173_historical_center_x1_def:
  registered_case10173_historical_center_x1 =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F 4047025000000w)
        (BoundedSigned64 F 4047025000001w))
End

Definition registered_case10173_historical_center_x2_def:
  registered_case10173_historical_center_x2 =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F 4047025000000w)
        (BoundedSigned64 F 4047025000001w))
End

Definition registered_case10173_historical_center_x3_def:
  registered_case10173_historical_center_x3 =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F 4033203125000w)
        (BoundedSigned64 F 4033203125001w))
End

Definition registered_case10173_historical_center_x4_def:
  registered_case10173_historical_center_x4 =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F 4033203125000w)
        (BoundedSigned64 F 4033203125001w))
End

Definition registered_case10173_historical_center_x5_def:
  registered_case10173_historical_center_x5 =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F 4066406250000w)
        (BoundedSigned64 F 4066406250001w))
End

Definition registered_case10173_historical_center_environment_object_def:
  registered_case10173_historical_center_environment_object =
    registered_case10173_cv_list
      [registered_case10173_historical_center_x0;
       registered_case10173_historical_center_x1;
       registered_case10173_historical_center_x2;
       registered_case10173_historical_center_x3;
       registered_case10173_historical_center_x4;
       registered_case10173_historical_center_x5]
End

Theorem registered_case10173_historical_center_environment_packet_exact:
  registered_case10173_historical_center_environment_object =
    bounded_interval64_object_cv_list
      (bounded_case10173_packet_center_environment
        bounded_case10173_decimal_packet0_source_aligned)
Proof
  simp
    [registered_case10173_historical_center_environment_object_def,
     registered_case10173_historical_center_x0_def,
     registered_case10173_historical_center_x1_def,
     registered_case10173_historical_center_x2_def,
     registered_case10173_historical_center_x3_def,
     registered_case10173_historical_center_x4_def,
     registered_case10173_historical_center_x5_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
     compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
     compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
QED

Theorem registered_case10173_historical_center_u126_local_object:
  ?value g0 g1 g2.
    registered_case10173_fs_hist_u_three_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x5 =
    SOME
      (Pair value (registered_case10173_cv_list [g0;g1;g2]))
Proof
  simp
    [registered_case10173_historical_center_x0_def,
     registered_case10173_historical_center_x1_def,
     registered_case10173_historical_center_x5_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_center_u135_local_object:
  ?value g0 g1 g2.
    registered_case10173_fs_hist_u_three_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x4 =
    SOME
      (Pair value (registered_case10173_cv_list [g0;g1;g2]))
Proof
  simp
    [registered_case10173_historical_center_x0_def,
     registered_case10173_historical_center_x2_def,
     registered_case10173_historical_center_x4_def,
     compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
     compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
  >> EVAL_TAC
  >> simp []
QED

Theorem registered_case10173_historical_center_u126_eval:
  registered_case10173_fs_hist_u_three_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x1
      registered_case10173_historical_center_x5 =
      SOME (Pair value (registered_case10173_cv_list [g0;g1;g2])) /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv
          (registered_case10173_cv_list
            [registered_case10173_historical_center_x0;
             registered_case10173_historical_center_x1;
             registered_case10173_historical_center_x2;
             registered_case10173_historical_center_x3;
             registered_case10173_historical_center_x4;
             registered_case10173_historical_center_x5])])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair value
            (registered_case10173_cv_list
              [g0;g1;registered_case10173_interval_zero_cv;
               registered_case10173_interval_zero_cv;
               registered_case10173_interval_zero_cv;g2]))),
       refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u126_object_eval
  >> simp []
QED

Theorem registered_case10173_historical_center_u135_eval:
  registered_case10173_fs_hist_u_three_object
      registered_case10173_historical_center_x0
      registered_case10173_historical_center_x2
      registered_case10173_historical_center_x4 =
      SOME (Pair value (registered_case10173_cv_list [g0;g1;g2])) /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv
          (registered_case10173_cv_list
            [registered_case10173_historical_center_x0;
             registered_case10173_historical_center_x1;
             registered_case10173_historical_center_x2;
             registered_case10173_historical_center_x3;
             registered_case10173_historical_center_x4;
             registered_case10173_historical_center_x5])])
      (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair value
            (registered_case10173_cv_list
              [g0;registered_case10173_interval_zero_cv;g1;
               registered_case10173_interval_zero_cv;g2;
               registered_case10173_interval_zero_cv]))),
       refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalUObjectEmbeddingEvalTheory.registered_case10173_fs_hist_u135_object_eval
  >> simp []
QED

val _ = export_theory ();
