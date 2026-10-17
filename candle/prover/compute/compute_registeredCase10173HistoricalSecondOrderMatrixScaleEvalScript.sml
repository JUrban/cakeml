(*****************************************************************************
 * Registered two-stage matrix scaling for the historical second-order jet.
 *
 * The source deliberately multiplies every interval without rounding and
 * rounds the resulting matrix in a second pass.  The intermediate raw matrix
 * is kept explicit here, so the evaluator theorem follows that literal source
 * boundary while the final theorem exposes the typed bounded result.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalSecondOrderMatrixScaleEval
Ancestors
  compute_registeredCase10173HistoricalSecondOrderMatrixEval
  compute_registeredCase10173HistoricalListScaleRefinement
Libs
  bossLib preamble intLib

Definition registered_case10173_cv_matrix_def:
  registered_case10173_cv_matrix rows =
    registered_case10173_cv_list (MAP registered_case10173_cv_list rows)
End

Theorem registered_case10173_cv_matrix_cons:
  registered_case10173_cv_matrix (row::rows) =
    Pair (registered_case10173_cv_list row)
      (registered_case10173_cv_matrix rows)
Proof
  simp
    [registered_case10173_cv_matrix_def,
     compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
QED

Definition registered_case10173_fs_raw_interval_matrix_scale_object_def:
  registered_case10173_fs_raw_interval_matrix_scale_object scalar
      ([]:cv list list) = SOME [] /\
  registered_case10173_fs_raw_interval_matrix_scale_object scalar
      (row::rows) =
    case registered_case10173_fs_raw_interval_list_scale_object scalar row of
    | NONE => NONE
    | SOME scaled_row =>
      case registered_case10173_fs_raw_interval_matrix_scale_object
        scalar rows of
      | NONE => NONE
      | SOME scaled_rows => SOME (scaled_row::scaled_rows)
End

Definition registered_case10173_fs_raw_interval_matrix_round_object_def:
  registered_case10173_fs_raw_interval_matrix_round_object denominator
      ([]:cv list list) = SOME [] /\
  registered_case10173_fs_raw_interval_matrix_round_object denominator
      (row::rows) =
    case registered_case10173_fs_raw_interval_list_round_object
      denominator row of
    | NONE => NONE
    | SOME rounded_row =>
      case registered_case10173_fs_raw_interval_matrix_round_object
        denominator rows of
      | NONE => NONE
      | SOME rounded_rows => SOME (rounded_row::rounded_rows)
End

Definition registered_case10173_fsn_interval_matrix_scale_object_def:
  registered_case10173_fsn_interval_matrix_scale_object scalar
      ([]:cv list list) = SOME [] /\
  registered_case10173_fsn_interval_matrix_scale_object scalar
      (row::rows) =
    case registered_case10173_fsn_interval_list_scale_object scalar row of
    | NONE => NONE
    | SOME scaled_row =>
      case registered_case10173_fsn_interval_matrix_scale_object scalar rows of
      | NONE => NONE
      | SOME scaled_rows => SOME (scaled_row::scaled_rows)
End

Definition registered_case10173_fs_raw_interval_matrix_scale_body_def:
  registered_case10173_fs_raw_interval_matrix_scale_body =
    If (Uop Ispair (Var «row_lists»))
      (Pair
        (App «candle_cv_fs_raw_interval_list_scale»
          [Var «scalar»;Uop Fst (Var «row_lists»)])
        (App «candle_cv_fs_raw_interval_matrix_scale»
          [Var «scalar»;Uop Snd (Var «row_lists»)]))
      (Num 0)
End

Definition registered_case10173_fs_raw_interval_matrix_round_body_def:
  registered_case10173_fs_raw_interval_matrix_round_body =
    If (Uop Ispair (Var «row_lists»))
      (Pair
        (App «candle_cv_fs_raw_interval_list_round»
          [Var «denominator»;Uop Fst (Var «row_lists»)])
        (App «candle_cv_fs_raw_interval_matrix_round»
          [Var «denominator»;Uop Snd (Var «row_lists»)]))
      (Num 0)
End

Definition registered_case10173_fs_hist_matrix_scale_body_def:
  registered_case10173_fs_hist_matrix_scale_body =
    App «candle_cv_fs_raw_interval_matrix_round»
      [App «candle_cv_fs_scale» [];
       App «candle_cv_fs_raw_interval_matrix_scale»
         [Var «scalar»;Var «matrixvalue»]]
End

Theorem registered_case10173_fs_raw_interval_matrix_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_matrix_scale» =
    SOME
      ([«scalar»;«row_lists»],
       registered_case10173_fs_raw_interval_matrix_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_matrix_round_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_raw_interval_matrix_round» =
    SOME
      ([«denominator»;«row_lists»],
       registered_case10173_fs_raw_interval_matrix_round_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_matrix_scale_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_matrix_scale» =
    SOME
      ([«scalar»;«matrixvalue»],
       registered_case10173_fs_hist_matrix_scale_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_raw_interval_matrix_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_scale»
        [from_cv scalar;from_cv (registered_case10173_cv_matrix rows)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«scalar»,from_cv scalar);
         («row_lists»,from_cv (registered_case10173_cv_matrix rows))]
        registered_case10173_fs_raw_interval_matrix_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_matrix_scale_lookup]
QED

Theorem registered_case10173_fs_raw_interval_matrix_round_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_interval_matrix_round»
        [from_cv (Num denominator);
         from_cv (registered_case10173_cv_matrix rows)])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«denominator»,from_cv (Num denominator));
         («row_lists»,from_cv (registered_case10173_cv_matrix rows))]
        registered_case10173_fs_raw_interval_matrix_round_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_raw_interval_matrix_round_lookup]
QED

Theorem registered_case10173_fs_hist_matrix_scale_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_matrix_scale»
        [from_cv scalar;from_cv matrixvalue])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«scalar»,from_cv scalar);(«matrixvalue»,from_cv matrixvalue)]
        registered_case10173_fs_hist_matrix_scale_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_hist_matrix_scale_lookup]
QED

Theorem registered_case10173_fs_raw_interval_matrix_scale_object_shape:
  !scalar rows scaled_rows.
    registered_case10173_fs_raw_interval_matrix_scale_object
      scalar rows = SOME scaled_rows ==>
    MAP LENGTH scaled_rows = MAP LENGTH rows
Proof
  Induct_on `rows`
  >> rw [registered_case10173_fs_raw_interval_matrix_scale_object_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_length
  >> res_tac
  >> gvs []
QED

Theorem registered_case10173_fs_raw_interval_matrix_scale_object_eval:
  !scalar rows scaled_rows clock refs.
    registered_case10173_fs_raw_interval_matrix_scale_object
      scalar rows = SOME scaled_rows /\
    SUM (MAP LENGTH rows) + LENGTH rows + 3 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_scale»
          [from_cv scalar;from_cv (registered_case10173_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_matrix scaled_rows)),refs)
Proof
  Induct_on `rows`
  >- (rpt strip_tac
      >> gvs
           [registered_case10173_fs_raw_interval_matrix_scale_object_def]
      >> rw [registered_case10173_fs_raw_interval_matrix_scale_unfold]
      >> simp
           [registered_case10173_fs_raw_interval_matrix_scale_body_def,
            registered_case10173_cv_matrix_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_scale_object scalar h`
  >> gvs [registered_case10173_fs_raw_interval_matrix_scale_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_matrix_scale_object scalar rows`
  >> gvs [registered_case10173_fs_raw_interval_matrix_scale_object_def]
  >> fs [registered_case10173_fs_raw_interval_matrix_scale_object_def]
  >> gvs []
  >> rw [registered_case10173_fs_raw_interval_matrix_scale_unfold]
  >> simp
       [registered_case10173_fs_raw_interval_matrix_scale_body_def,
        registered_case10173_cv_matrix_cons,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (registered_case10173_cv_list h)
                 (registered_case10173_cv_matrix rows):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `registered_case10173_cv_list x`,
            `right_result` |-> `registered_case10173_cv_matrix x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_scale»
            [from_cv scalar;
             Uop Fst
               (Pair (from_cv (registered_case10173_cv_list h))
                 (from_cv (registered_case10173_cv_matrix rows)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_scale»
            [from_cv scalar;from_cv (registered_case10173_cv_list h)]) refs` by
       (irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results)
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> irule
           compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_scale_object_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_scale»
          [from_cv scalar;
           Uop Snd
             (Pair (from_cv (registered_case10173_cv_list h))
               (from_cv (registered_case10173_cv_matrix rows)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_scale»
          [from_cv scalar;from_cv (registered_case10173_cv_matrix rows)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
        >> intLib.ARITH_TAC)
  >> rw []
  >> first_x_assum irule
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_raw_interval_matrix_round_object_eval:
  !denominator rows rounded_rows clock refs.
    registered_case10173_fs_raw_interval_matrix_round_object
      denominator rows = SOME rounded_rows /\
    0 < denominator /\
    SUM (MAP LENGTH rows) + LENGTH rows + 11 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_round»
          [from_cv (Num denominator);
           from_cv (registered_case10173_cv_matrix rows)])
        (refs:hol_refs) =
      (M_success
        (from_cv (registered_case10173_cv_matrix rounded_rows)),refs)
Proof
  Induct_on `rows`
  >- (rpt strip_tac
      >> fs
           [registered_case10173_fs_raw_interval_matrix_round_object_def]
      >> rw
           [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              (Q.INST [`rows` |-> `[]:cv list list`]
                registered_case10173_fs_raw_interval_matrix_round_unfold)]
      >> simp
           [registered_case10173_fs_raw_interval_matrix_round_body_def,
            registered_case10173_cv_matrix_def,
            compute_evalTheory.subst_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
            compute_execTheory.from_cv_def,
            Once compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,
            compute_evalTheory.do_ispair_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def])
  >> rpt strip_tac
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_round_object denominator h`
  >> gvs [registered_case10173_fs_raw_interval_matrix_round_object_def]
  >> Cases_on
       `registered_case10173_fs_raw_interval_matrix_round_object denominator rows`
  >> gvs [registered_case10173_fs_raw_interval_matrix_round_object_def]
  >> fs [registered_case10173_fs_raw_interval_matrix_round_object_def]
  >> gvs []
  >> fs [registered_case10173_fs_raw_interval_matrix_round_object_def]
  >> gvs []
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_raw_interval_matrix_round_unfold]
  >> simp
       [registered_case10173_fs_raw_interval_matrix_round_body_def,
        registered_case10173_cv_matrix_cons,
        compute_evalTheory.subst_def,
        compute_execTheory.from_cv_def]
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`argument` |->
               `(Pair (registered_case10173_cv_list h)
                 (registered_case10173_cv_matrix rows):cv)`]
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_if_ispair_from_cv)]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`left_result` |-> `registered_case10173_cv_list x`,
            `right_result` |-> `registered_case10173_cv_matrix x'`]
           compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results))
  >> conj_tac
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_round»
            [from_cv (Num denominator);
             Uop Fst
               (Pair (from_cv (registered_case10173_cv_list h))
                 (from_cv (registered_case10173_cv_matrix rows)))]) refs =
        compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_raw_interval_list_round»
            [from_cv (Num denominator);
             from_cv (registered_case10173_cv_list h)]) refs` by
       (irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results)
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components]
        >> intLib.ARITH_TAC)
      >> rw []
      >> fs [compute_execTheory.from_cv_def]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fs_raw_interval_list_round_object_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_round»
          [from_cv (Num denominator);
           Uop Snd
             (Pair (from_cv (registered_case10173_cv_list h))
               (from_cv (registered_case10173_cv_matrix rows)))]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_round»
          [from_cv (Num denominator);
           from_cv (registered_case10173_cv_matrix rows)]) refs` by
       (irule
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results)
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components]
        >> intLib.ARITH_TAC)
  >> rw []
  >> fs [compute_execTheory.from_cv_def]
  >> first_x_assum irule
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fsn_interval_matrix_scale_decompose:
  !scalar rows scaled_rows.
    registered_case10173_fsn_interval_matrix_scale_object scalar rows =
      SOME scaled_rows ==>
    ?raw_rows.
      registered_case10173_fs_raw_interval_matrix_scale_object scalar rows =
        SOME raw_rows /\
      registered_case10173_fs_raw_interval_matrix_round_object
        1000000000000 raw_rows = SOME scaled_rows
Proof
  Induct_on `rows`
  >- (rw [registered_case10173_fsn_interval_matrix_scale_object_def]
      >> qexists_tac `[]`
      >> simp
           [registered_case10173_fs_raw_interval_matrix_scale_object_def,
            registered_case10173_fs_raw_interval_matrix_round_object_def])
  >> rw [registered_case10173_fsn_interval_matrix_scale_object_def]
  >> every_case_tac
  >> gvs [compute_registeredCase10173HistoricalListArithmeticEvalTheory.registered_case10173_fsn_interval_list_scale_object_def]
  >> first_x_assum drule
  >> strip_tac
  >> Cases_on
       `registered_case10173_fs_raw_interval_list_scale_object scalar h`
  >> gvs []
  >> qexists_tac `x''::raw_rows`
  >> simp
       [registered_case10173_fs_raw_interval_matrix_scale_object_def,
        registered_case10173_fs_raw_interval_matrix_round_object_def]
QED

Theorem registered_case10173_fsn_interval_matrix_scale_object_eval:
  registered_case10173_fsn_interval_matrix_scale_object scalar rows =
      SOME scaled_rows /\
  SUM (MAP LENGTH rows) + LENGTH rows + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_matrix_scale»
        [from_cv scalar;from_cv (registered_case10173_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_cv_matrix scaled_rows)),refs)
Proof
  strip_tac
  >> drule registered_case10173_fsn_interval_matrix_scale_decompose
  >> disch_then (qx_choose_then `raw_rows` strip_assume_tac)
  >> imp_res_tac registered_case10173_fs_raw_interval_matrix_scale_object_shape
  >> rw [registered_case10173_fs_hist_matrix_scale_unfold]
  >> simp
       [registered_case10173_fs_hist_matrix_scale_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_scale» []) refs =
      (M_success (Num 1000000000000),refs)` by
       (irule
          compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_scale»
          [from_cv scalar;
           from_cv (registered_case10173_cv_matrix rows)]) refs =
      (M_success (from_cv (registered_case10173_cv_matrix raw_rows)),refs)` by
       (irule registered_case10173_fs_raw_interval_matrix_scale_object_eval
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_round»
          [App «candle_cv_fs_scale» [];
           App «candle_cv_fs_raw_interval_matrix_scale»
             [from_cv scalar;
              from_cv (registered_case10173_cv_matrix rows)]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_matrix_round»
          [from_cv (Num 1000000000000);
           from_cv (registered_case10173_cv_matrix raw_rows)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [compute_execTheory.from_cv_def])
  >> rw []
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_raw_interval_matrix_round_object_eval)
  >> simp []
  >> `LENGTH raw_rows = LENGTH rows` by
       metis_tac [listTheory.LENGTH_MAP]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_cv_matrix_map_bounded_interval64_object_cv:
  !rows.
    registered_case10173_cv_matrix
      (MAP (MAP bounded_interval64_object_cv) rows) =
    bounded_interval64_object_cv_matrix rows
Proof
  Induct
  >- simp
       [registered_case10173_cv_matrix_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def]
  >> simp
       [registered_case10173_cv_matrix_cons,
        compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_cv_list_map_bounded_interval64_object_cv,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def]
QED

Theorem registered_case10173_fsn_interval_matrix_scale_object_bounded:
  !scalar rows object_result.
    bounded_object_fs_interval_matrix_scale_decimal scalar rows =
      SOME object_result ==>
    ?scaled_rows.
      registered_case10173_fsn_interval_matrix_scale_object
        (bounded_interval64_object_cv scalar)
        (MAP (MAP bounded_interval64_object_cv) rows) = SOME scaled_rows /\
      registered_case10173_cv_matrix scaled_rows = object_result
Proof
  Induct_on `rows`
  >- (rw
        [compute_boundedObjectTaylorStateDecimalTheory.bounded_object_fs_interval_matrix_scale_decimal_def]
      >> qexists_tac `[]`
      >> simp
           [registered_case10173_fsn_interval_matrix_scale_object_def,
            registered_case10173_cv_matrix_def,
            compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def])
  >> rpt strip_tac
  >> Cases_on `bounded_object_fs_interval_list_scale_decimal scalar h`
  >> gvs
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_object_fs_interval_matrix_scale_decimal_def]
  >> Cases_on `bounded_object_fs_interval_matrix_scale_decimal scalar rows`
  >> gvs
       [compute_boundedObjectTaylorStateDecimalTheory.bounded_object_fs_interval_matrix_scale_decimal_def]
  >> drule
       compute_registeredCase10173HistoricalListScaleRefinementTheory.registered_case10173_fsn_interval_list_scale_object_bounded
  >> disch_then (qx_choose_then `scaled_row` strip_assume_tac)
  >> first_x_assum drule
  >> disch_then (qx_choose_then `scaled_rows` strip_assume_tac)
  >> qexists_tac `scaled_row::scaled_rows`
  >> simp
       [registered_case10173_fsn_interval_matrix_scale_object_def,
        registered_case10173_cv_matrix_cons]
QED

Theorem registered_case10173_fs_hist_matrix_scale_typed_eval:
  bounded_interval64_matrix_scale_decimal scalar rows = SOME scaled_rows /\
  SUM (MAP LENGTH rows) + LENGTH rows + 12 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_matrix_scale»
        [from_cv (bounded_interval64_object_cv scalar);
         from_cv (bounded_interval64_object_cv_matrix rows)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix scaled_rows)),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedObjectTaylorStateDecimalTheory.bounded_object_fs_interval_matrix_scale_decimal_exact
  >> drule registered_case10173_fsn_interval_matrix_scale_object_bounded
  >> disch_then (qx_choose_then `object_rows` strip_assume_tac)
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_matrix_scale»
          [from_cv (bounded_interval64_object_cv scalar);
           from_cv
             (registered_case10173_cv_matrix
               (MAP (MAP bounded_interval64_object_cv) rows))]) refs =
      (M_success
        (from_cv (registered_case10173_cv_matrix object_rows)),refs)` by
       (irule registered_case10173_fsn_interval_matrix_scale_object_eval
        >> simp [listTheory.MAP_MAP_o, combinTheory.o_DEF]
        >> metis_tac [arithmeticTheory.ADD_COMM, arithmeticTheory.ADD_ASSOC])
  >> gvs [registered_case10173_cv_matrix_map_bounded_interval64_object_cv]
QED

val _ = export_theory ();
