(*****************************************************************************
 * Registered evaluator semantics for signed historical arctangent points.
 *
 * The source selects the positive lower/upper polynomial by the sign of the
 * endpoint, projects the required enclosure endpoint, and negates it in the
 * negative case.  These lemmas connect that literal source control flow to
 * the bounded-object unit-endpoint checker.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalAtanPointEval
Ancestors
  compute_registeredCase10173HistoricalAtanEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_hist_atan_lower_point_body_def:
  registered_case10173_fs_hist_atan_lower_point_body =
    If (App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];Var «x»])
      (Uop Fst (App «candle_cv_fs_hist_atan_pos_lower» [Var «x»]))
      (App «candle_cv_fs_raw_neg»
        [Uop Snd
          (App «candle_cv_fs_hist_atan_pos_upper»
            [App «candle_cv_fs_raw_neg» [Var «x»]])])
End

Definition registered_case10173_fs_hist_atan_upper_point_body_def:
  registered_case10173_fs_hist_atan_upper_point_body =
    If (App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];Var «x»])
      (Uop Snd (App «candle_cv_fs_hist_atan_pos_upper» [Var «x»]))
      (App «candle_cv_fs_raw_neg»
        [Uop Fst
          (App «candle_cv_fs_hist_atan_pos_lower»
            [App «candle_cv_fs_raw_neg» [Var «x»]])])
End

Theorem registered_case10173_fs_hist_atan_lower_point_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_atan_lower_point» =
    SOME ([«x»],registered_case10173_fs_hist_atan_lower_point_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_atan_upper_point_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_atan_upper_point» =
    SOME ([«x»],registered_case10173_fs_hist_atan_upper_point_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_atan_lower_point_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_lower_point» [from_cv input])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv input)]
        registered_case10173_fs_hist_atan_lower_point_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_atan_lower_point_lookup]
QED

Theorem registered_case10173_fs_hist_atan_upper_point_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_upper_point» [from_cv input])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv input)]
        registered_case10173_fs_hist_atan_upper_point_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_atan_upper_point_lookup]
QED

Theorem registered_case10173_compute_eval_uop_fst_argument_result:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (from_cv (Pair left right)),refs) ==>
  compute_eval clock ceqs (Uop Fst expression) refs =
    (M_success (from_cv left),refs)
Proof
  strip_tac
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_compute_eval_uop_snd_argument_result:
  compute_eval clock ceqs expression (refs:hol_refs) =
      (M_success (from_cv (Pair left right)),refs) ==>
  compute_eval clock ceqs (Uop Snd expression) refs =
    (M_success (from_cv right),refs)
Proof
  strip_tac
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_zero_le_endpoint_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_raw_le»
        [App «candle_cv_fs_zero» [];
         from_cv (bounded_signed64_object_cv endpoint)])
      (refs:hol_refs) =
    (M_success
      (Num
        (if ~bounded_signed64_effective_negative endpoint then 1 else 0)),
     refs)
Proof
  strip_tac
  >> `bounded_object_fs_raw_le
        (Pair (Num 0) (Num 0))
        (bounded_signed64_object_cv endpoint) =
      SOME (~bounded_signed64_effective_negative endpoint)` by
       (Cases_on `endpoint`
        >> rename1 `BoundedSigned64 negative magnitude`
        >> Cases_on `negative`
        >> Cases_on `magnitude = 0w`
        >> simp
             [compute_boundedObjectDecimalOrderTheory.bounded_object_fs_raw_le_def,
              compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
              compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
              wordsTheory.w2n_eq_0])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];
           from_cv (bounded_signed64_object_cv endpoint)]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le»
          [from_cv (Pair (Num 0) (Num 0));
           from_cv (bounded_signed64_object_cv endpoint)]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp
             [compute_execProofTheory.compute_eval_from_cv,
              compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_zero_eval])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le»
          [from_cv (Pair (Num 0) (Num 0));
           from_cv (bounded_signed64_object_cv endpoint)]) refs =
      (M_success
        (Num
          (if ~bounded_signed64_effective_negative endpoint then 1 else 0)),
       refs)` by
       (irule
          compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_le_eval
        >> simp [])
  >> metis_tac []
QED

Theorem registered_case10173_fs_hist_atan_lower_point_nonnegative_eval:
  ~bounded_signed64_effective_negative endpoint /\
  bounded_object_fs_interval64_atan_pos_lower_decimal
      (bounded_signed64_magnitude endpoint) =
    SOME (Pair lower upper) /\
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_lower_point»
        [from_cv (bounded_signed64_object_cv endpoint)])
      (refs:hol_refs) =
    (M_success (from_cv lower),refs)
Proof
  rpt strip_tac
  >> `bounded_signed64_object_cv endpoint =
      registered_case10173_hist_positive_endpoint_object
        (bounded_signed64_magnitude endpoint)` by
       (Cases_on `endpoint`
        >> rename1 `BoundedSigned64 negative magnitude`
        >> Cases_on `negative`
        >> Cases_on `magnitude = 0w`
        >> gvs
             [compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
              compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
              compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
              registered_case10173_hist_positive_endpoint_object_def,
              wordsTheory.w2n_eq_0])
  >> simp [registered_case10173_fs_hist_atan_lower_point_unfold]
  >> simp
       [registered_case10173_fs_hist_atan_lower_point_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];
           from_cv (bounded_signed64_object_cv endpoint)]) refs =
      (M_success (Num 1),refs)` by
       (mp_tac
          (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
            registered_case10173_fs_zero_le_endpoint_eval)
        >> simp []
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];
           from_cv
             (registered_case10173_hist_positive_endpoint_object
               (bounded_signed64_magnitude endpoint))]) refs =
      (M_success (Num 1),refs)` by metis_tac []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule registered_case10173_compute_eval_uop_fst_argument_result
  >> rw []
  >> qexists_tac `upper`
  >> mp_tac
       (Q.INST
         [`clock` |-> `clock - 1`,
          `magnitude` |-> `bounded_signed64_magnitude endpoint`,
          `result` |-> `Pair lower upper`, `refs` |-> `refs`]
         compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_hist_atan_pos_lower_eval)
  >> simp [compute_execTheory.from_cv_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_atan_lower_point_negative_eval:
  bounded_signed64_effective_negative endpoint /\
  bounded_object_fs_interval64_atan_pos_upper_decimal
      (bounded_signed64_magnitude endpoint) =
    SOME (Pair lower upper) /\
  bounded_object_fs_raw_neg upper = SOME result /\
  31 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_lower_point»
        [from_cv (bounded_signed64_object_cv endpoint)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> `bounded_signed64_object_cv (bounded_signed64_neg endpoint) =
      registered_case10173_hist_positive_endpoint_object
        (bounded_signed64_magnitude endpoint)` by
       (Cases_on `endpoint`
        >> rename1 `BoundedSigned64 negative magnitude`
        >> Cases_on `negative`
        >> Cases_on `magnitude = 0w`
        >> gvs
             [compute_boundedSignedEndpointTheory.bounded_signed64_effective_negative_def,
              compute_boundedSignedEndpointTheory.bounded_signed64_magnitude_def,
              compute_boundedSignedEndpointAddTheory.bounded_signed64_neg_def,
              compute_boundedSignedEndpointTheory.bounded_signed64_make_def,
              compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def,
              registered_case10173_hist_positive_endpoint_object_def,
              wordsTheory.w2n_eq_0])
  >> simp [registered_case10173_fs_hist_atan_lower_point_unfold]
  >> simp
       [registered_case10173_fs_hist_atan_lower_point_body_def,
        compute_evalTheory.subst_def]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_le»
          [App «candle_cv_fs_zero» [];
           from_cv (bounded_signed64_object_cv endpoint)]) refs =
      (M_success (Num 0),refs)` by
       (mp_tac
          (Q.INST [`clock` |-> `clock - 1`, `refs` |-> `refs`]
            registered_case10173_fs_zero_le_endpoint_eval)
        >> simp []
        >> intLib.ARITH_TAC)
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `25 < clock - 1` by intLib.ARITH_TAC
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_neg»
          [from_cv (bounded_signed64_object_cv endpoint)]) refs =
      (M_success
        (from_cv
          (registered_case10173_hist_positive_endpoint_object
            (bounded_signed64_magnitude endpoint))),refs)` by
       (mp_tac
          (Q.INST
            [`clock` |-> `clock - 1`,
             `value` |-> `bounded_signed64_object_cv endpoint`,
             `result` |->
               `bounded_signed64_object_cv
                 (bounded_signed64_neg endpoint)`,
             `refs` |-> `refs`]
            compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_eval)
        >> simp
             [compute_boundedObjectDecimalAddTheory.bounded_object_fs_raw_neg_object_cv]
        >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_pos_upper»
          [App «candle_cv_fs_raw_neg»
            [from_cv (bounded_signed64_object_cv endpoint)]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_pos_upper»
          [from_cv
            (registered_case10173_hist_positive_endpoint_object
              (bounded_signed64_magnitude endpoint))]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_pos_upper»
          [from_cv
            (registered_case10173_hist_positive_endpoint_object
              (bounded_signed64_magnitude endpoint))]) refs =
      (M_success (from_cv (Pair lower upper)),refs)` by
       (match_mp_tac
          (Q.INST
            [`clock` |-> `clock - 1`,
             `magnitude` |-> `bounded_signed64_magnitude endpoint`,
             `result` |-> `Pair lower upper`, `refs` |-> `refs`]
            compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_hist_atan_pos_upper_eval)
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_hist_atan_pos_upper»
          [App «candle_cv_fs_raw_neg»
            [from_cv (bounded_signed64_object_cv endpoint)]]) refs =
      (M_success (from_cv (Pair lower upper)),refs)` by
       simp []
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Uop Snd
          (App «candle_cv_fs_hist_atan_pos_upper»
            [App «candle_cv_fs_raw_neg»
              [from_cv (bounded_signed64_object_cv endpoint)]])) refs =
      (M_success (from_cv upper),refs)` by
       (irule registered_case10173_compute_eval_uop_snd_argument_result
        >> qexists_tac `lower`
        >> simp [])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_neg»
          [Uop Snd
            (App «candle_cv_fs_hist_atan_pos_upper»
              [App «candle_cv_fs_raw_neg»
                [from_cv (bounded_signed64_object_cv endpoint)]])]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_neg» [from_cv upper]) refs` by
       (irule
          compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
        >> conj_tac >- intLib.ARITH_TAC
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
