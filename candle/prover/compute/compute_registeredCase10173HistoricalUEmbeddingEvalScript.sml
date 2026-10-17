(*****************************************************************************
 * Registered evaluator semantics for embedding the historical three-variable
 * u calculation into the u126 and u135 six-coordinate results.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalUEmbeddingEval
Ancestors
  compute_registeredCase10173HistoricalDeltaX4GradientEval
  compute_registeredCase10173CanonicalListEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_u126_body_def:
  registered_case10173_fs_hist_u126_body =
    Let «local»
      (App «candle_cv_fs_hist_u_three»
        [App «candle_cv_fs_interval_lookup»
           [Num 0;Var «environment»];
         App «candle_cv_fs_interval_lookup»
           [Num 1;Var «environment»];
         App «candle_cv_fs_interval_lookup»
           [Num 5;Var «environment»]])
      (Pair
        (Uop Fst (Var «local»))
        (App «candle_cv_fs_angle_six»
          [App «candle_cv_fs_interval_lookup»
             [Num 0;Uop Snd (Var «local»)];
           App «candle_cv_fs_interval_lookup»
             [Num 1;Uop Snd (Var «local»)];
           App «candle_cv_fs_interval_zero» [];
           App «candle_cv_fs_interval_zero» [];
           App «candle_cv_fs_interval_zero» [];
           App «candle_cv_fs_interval_lookup»
             [Num 2;Uop Snd (Var «local»)]]))
End

Definition registered_case10173_fs_hist_u135_body_def:
  registered_case10173_fs_hist_u135_body =
    Let «local»
      (App «candle_cv_fs_hist_u_three»
        [App «candle_cv_fs_interval_lookup»
           [Num 0;Var «environment»];
         App «candle_cv_fs_interval_lookup»
           [Num 2;Var «environment»];
         App «candle_cv_fs_interval_lookup»
           [Num 4;Var «environment»]])
      (Pair
        (Uop Fst (Var «local»))
        (App «candle_cv_fs_angle_six»
          [App «candle_cv_fs_interval_lookup»
             [Num 0;Uop Snd (Var «local»)];
           App «candle_cv_fs_interval_zero» [];
           App «candle_cv_fs_interval_lookup»
             [Num 1;Uop Snd (Var «local»)];
           App «candle_cv_fs_interval_zero» [];
           App «candle_cv_fs_interval_lookup»
             [Num 2;Uop Snd (Var «local»)];
           App «candle_cv_fs_interval_zero» []]))
End

Theorem registered_case10173_fs_hist_u126_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_u126» =
    SOME ([«environment»],registered_case10173_fs_hist_u126_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_u135_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_u135» =
    SOME ([«environment»],registered_case10173_fs_hist_u135_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_u126_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126» [from_cv environment])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_u126_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_u126_lookup]
QED

Theorem registered_case10173_fs_hist_u135_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135» [from_cv environment])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«environment»,from_cv environment)]
        registered_case10173_fs_hist_u135_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_u135_lookup]
QED

Theorem registered_case10173_fs_interval_lookup_uop_snd_local3_eval:
  index < 3 /\
  EL index [g0;g1;g2] = result /\
  index + 4 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_lookup»
        [Num index;
         Uop Snd
           (Pair (from_cv value)
             (from_cv
               (registered_case10173_cv_list [g0;g1;g2])))])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_lookup»
            [from_cv (Num index);
             from_cv
               (registered_case10173_cv_list [g0;g1;g2])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp
           [compute_execTheory.from_cv_def,
            compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
      >> simp
           [compute_evalTheory.compute_eval_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> simp [compute_execTheory.from_cv_def]
  >> irule
       compute_registeredCase10173HistoricalDeltaX4ValueEvalTheory.registered_case10173_fs_interval_lookup_cv_list_result_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_u126_from_local_eval:
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [App «candle_cv_fs_interval_lookup»
           [Num 0;
            from_cv
              (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])];
         App «candle_cv_fs_interval_lookup»
           [Num 1;
            from_cv
              (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])];
         App «candle_cv_fs_interval_lookup»
           [Num 5;
            from_cv
              (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair value
          (registered_case10173_cv_list [g0;g1;g2]))),refs) /\
  15 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u126»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])]) refs =
    (M_success
      (from_cv
        (Pair value
          (registered_case10173_cv_list
            [g0;g1;registered_case10173_interval_zero_cv;
             registered_case10173_interval_zero_cv;
             registered_case10173_interval_zero_cv;g2]))),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_u126_unfold]
  >> simp
       [registered_case10173_fs_hist_u126_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (Pair value
            (registered_case10173_cv_list [g0;g1;g2]))`
  >> conj_tac >- simp []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv g0;from_cv g1;
             from_cv registered_case10173_interval_zero_cv;
             from_cv registered_case10173_interval_zero_cv;
             from_cv registered_case10173_interval_zero_cv;
             from_cv g2]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >- (irule registered_case10173_fs_interval_lookup_uop_snd_local3_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_interval_lookup_uop_snd_local3_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >- (simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
          >> intLib.ARITH_TAC)
      >- (simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
          >> intLib.ARITH_TAC)
      >- (simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
          >> intLib.ARITH_TAC)
      >> irule registered_case10173_fs_interval_lookup_uop_snd_local3_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_u135_from_local_eval:
  compute_eval (clock - 1) registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u_three»
        [App «candle_cv_fs_interval_lookup»
           [Num 0;
            from_cv
              (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])];
         App «candle_cv_fs_interval_lookup»
           [Num 2;
            from_cv
              (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])];
         App «candle_cv_fs_interval_lookup»
           [Num 4;
            from_cv
              (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair value
          (registered_case10173_cv_list [g0;g1;g2]))),refs) /\
  15 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_u135»
        [from_cv
          (registered_case10173_cv_list [x0;x1;x2;x3;x4;x5])]) refs =
    (M_success
      (from_cv
        (Pair value
          (registered_case10173_cv_list
            [g0;registered_case10173_interval_zero_cv;g1;
             registered_case10173_interval_zero_cv;g2;
             registered_case10173_interval_zero_cv]))),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_u135_unfold]
  >> simp
       [registered_case10173_fs_hist_u135_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (Pair value
            (registered_case10173_cv_list [g0;g1;g2]))`
  >> conj_tac >- simp []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv g0;
             from_cv registered_case10173_interval_zero_cv;
             from_cv g1;
             from_cv registered_case10173_interval_zero_cv;
             from_cv g2;
             from_cv registered_case10173_interval_zero_cv]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >- (irule registered_case10173_fs_interval_lookup_uop_snd_local3_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >- (simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_interval_lookup_uop_snd_local3_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >- (simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
          >> intLib.ARITH_TAC)
      >- (irule registered_case10173_fs_interval_lookup_uop_snd_local3_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp
           [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_interval_zero_cv_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_zero_eval]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
