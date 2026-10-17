(*****************************************************************************
 * Compact object/evaluator bridge for the complete historical u126/u135
 * calculations.  The pure object functions preserve the exact three-entry
 * local gradient shape expected by the registered six-coordinate wrappers.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUObjectEmbeddingEval
Ancestors
  compute_registeredCase10173HistoricalUThreeEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u126_embed_local_object_def:
  registered_case10173_fs_hist_u126_embed_local_object local =
    case local of
    | Num _ => NONE
    | Pair value gradients =>
      case gradients of
      | Num _ => NONE
      | Pair g0 rest0 =>
        case rest0 of
        | Num _ => NONE
        | Pair g1 rest1 =>
          case rest1 of
          | Num _ => NONE
          | Pair g2 rest2 =>
            case rest2 of
            | Pair _ _ => NONE
            | Num terminator =>
              if terminator = 0 then
                SOME
                  (Pair value
                    (registered_case10173_cv_list
                      [g0;g1;registered_case10173_interval_zero_cv;
                       registered_case10173_interval_zero_cv;
                       registered_case10173_interval_zero_cv;g2]))
              else NONE
End

Definition registered_case10173_fs_hist_u135_embed_local_object_def:
  registered_case10173_fs_hist_u135_embed_local_object local =
    case local of
    | Num _ => NONE
    | Pair value gradients =>
      case gradients of
      | Num _ => NONE
      | Pair g0 rest0 =>
        case rest0 of
        | Num _ => NONE
        | Pair g1 rest1 =>
          case rest1 of
          | Num _ => NONE
          | Pair g2 rest2 =>
            case rest2 of
            | Pair _ _ => NONE
            | Num terminator =>
              if terminator = 0 then
                SOME
                  (Pair value
                    (registered_case10173_cv_list
                      [g0;registered_case10173_interval_zero_cv;g1;
                       registered_case10173_interval_zero_cv;g2;
                       registered_case10173_interval_zero_cv]))
              else NONE
End

Definition registered_case10173_fs_hist_u126_object_def:
  registered_case10173_fs_hist_u126_object x0 x1 x2 x3 x4 x5 =
    case registered_case10173_fs_hist_u_three_object x0 x1 x5 of
    | NONE => NONE
    | SOME local =>
      registered_case10173_fs_hist_u126_embed_local_object local
End

Definition registered_case10173_fs_hist_u135_object_def:
  registered_case10173_fs_hist_u135_object x0 x1 x2 x3 x4 x5 =
    case registered_case10173_fs_hist_u_three_object x0 x2 x4 of
    | NONE => NONE
    | SOME local =>
      registered_case10173_fs_hist_u135_embed_local_object local
End

Theorem registered_case10173_fs_hist_u_three_lookup_arguments_eval:
  registered_case10173_fs_hist_u_three_object x0 x1 x2 = SOME result /\
  90 < clock /\
  index0 < LENGTH values /\ index0 + 2 < clock /\
    EL index0 values = x0 /\
  index1 < LENGTH values /\ index1 + 2 < clock /\
    EL index1 values = x1 /\
  index2 < LENGTH values /\ index2 + 2 < clock /\
    EL index2 values = x2 ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [App «candle_cv_fs_interval_lookup»
           [Num index0;from_cv (registered_case10173_cv_list values)];
         App «candle_cv_fs_interval_lookup»
           [Num index1;from_cv (registered_case10173_cv_list values)];
         App «candle_cv_fs_interval_lookup»
           [Num index2;from_cv (registered_case10173_cv_list values)]])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_hist_u_three»
            [from_cv x0;from_cv x1;from_cv x2]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> simp []
      >> rpt conj_tac
      >- (irule
            compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >- (irule
            compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule
           compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalUThreeEvalTheory.registered_case10173_fs_hist_u_three_compact_object_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_u126_object_eval:
  registered_case10173_fs_hist_u_three_object x0 x1 x5 =
      SOME (Pair value (registered_case10173_cv_list [g0;g1;g2])) /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
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
       compute_registeredCase10173HistoricalUEmbeddingEvalTheory.registered_case10173_fs_hist_u126_from_local_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_hist_u_three_lookup_arguments_eval
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u135_object_eval:
  registered_case10173_fs_hist_u_three_object x0 x2 x4 =
      SOME (Pair value (registered_case10173_cv_list [g0;g1;g2])) /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
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
       compute_registeredCase10173HistoricalUEmbeddingEvalTheory.registered_case10173_fs_hist_u135_from_local_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> irule registered_case10173_fs_hist_u_three_lookup_arguments_eval
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u126_complete_object_eval:
  registered_case10173_fs_hist_u126_object x0 x1 x2 x3 x4 x5 =
      SOME result /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> Cases_on
       `registered_case10173_fs_hist_u_three_object x0 x1 x5`
  >> gvs [registered_case10173_fs_hist_u126_object_def]
  >> Cases_on `x`
  >> gvs [registered_case10173_fs_hist_u126_embed_local_object_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> irule
       (SIMP_RULE (srw_ss())
          [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
          registered_case10173_fs_hist_u126_object_eval)
  >> simp []
QED

Theorem registered_case10173_fs_hist_u135_complete_object_eval:
  registered_case10173_fs_hist_u135_object x0 x1 x2 x3 x4 x5 =
      SOME result /\
  100 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])])
      (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> Cases_on
       `registered_case10173_fs_hist_u_three_object x0 x2 x4`
  >> gvs [registered_case10173_fs_hist_u135_object_def]
  >> Cases_on `x`
  >> gvs [registered_case10173_fs_hist_u135_embed_local_object_def]
  >> every_case_tac
  >> gvs []
  >> simp
       [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> irule
       (SIMP_RULE (srw_ss())
          [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
          registered_case10173_fs_hist_u135_object_eval)
  >> simp []
QED

val _ = export_theory ();
