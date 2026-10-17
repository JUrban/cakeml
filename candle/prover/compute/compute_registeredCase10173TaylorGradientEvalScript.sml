(*****************************************************************************
 * Registered evaluator refinement for fixed-scale Taylor gradient bounds.
 *
 * The first theorem isolates one completed gradient row.  It composes the
 * registered source operations already refined for scaling, dot bounds,
 * interval addition and directed rounding.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorGradientEval
Ancestors
  compute_registeredCase10173TaylorRoundEval
Libs
  bossLib preamble

Definition registered_case10173_fs_gradient_center_interval_exp_def:
  registered_case10173_fs_gradient_center_interval_exp gradient =
    Pair
      (App «candle_cv_fs_raw_scale»
        [App «candle_cv_fs_scale» [];Uop Fst gradient])
      (App «candle_cv_fs_raw_scale»
        [App «candle_cv_fs_scale» [];Uop Snd gradient])
End

Definition registered_case10173_fs_gradient_variation_interval_exp_def:
  registered_case10173_fs_gradient_variation_interval_exp radii row =
    Pair
      (App «candle_cv_fs_raw_neg»
        [App «candle_cv_fs_dot_abs_upper» [radii;row]])
      (App «candle_cv_fs_dot_abs_upper» [radii;row])
End

Definition registered_case10173_fs_gradient_raw_interval_exp_def:
  registered_case10173_fs_gradient_raw_interval_exp radii gradient row =
    App «candle_cv_fs_raw_interval_add»
      [registered_case10173_fs_gradient_center_interval_exp gradient;
       registered_case10173_fs_gradient_variation_interval_exp radii row]
End

Definition registered_case10173_fs_gradient_row_exp_def:
  registered_case10173_fs_gradient_row_exp radii gradient row =
    App «candle_cv_fs_raw_interval_round»
      [App «candle_cv_fs_scale» [];
       registered_case10173_fs_gradient_raw_interval_exp
         radii gradient row]
End

Theorem registered_case10173_fs_gradient_row_object_eval:
  bounded_object_fs_gradient_row radii gradient row = SOME result /\
  64 * (LENGTH radii + 2) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_gradient_row_exp
        (from_cv (registered_case10173_word64_object_cv_list radii))
        (from_cv (bounded_interval64_object_cv gradient))
        (from_cv (bounded_interval64_object_cv_list row)))
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `gradient`
  >> rw
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_gradient_row_def]
  >> Cases_on `bounded_object_fs_dot_abs_upper radii row`
  >> gvs []
  >> rename1 `bounded_object_fs_dot_abs_upper radii row = SOME variation`
  >> Cases_on
       `bounded_object_fs_raw_scale 1000000000000
          (bounded_signed64_object_cv b)`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_scale 1000000000000
          (bounded_signed64_object_cv b) = SOME raw_lower`
  >> Cases_on
       `bounded_object_fs_raw_scale 1000000000000
          (bounded_signed64_object_cv b0)`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_scale 1000000000000
          (bounded_signed64_object_cv b0) = SOME raw_upper`
  >> Cases_on `bounded_object_fs_raw_neg variation`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_neg variation = SOME negative_variation`
  >> Cases_on
       `bounded_object_fs_raw_interval_add
          (Pair raw_lower raw_upper)
          (Pair negative_variation variation)`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_interval_add
          (Pair raw_lower raw_upper)
          (Pair negative_variation variation) = SOME raw_interval`
  >> Cases_on
       `bounded_object_fs_raw_interval_round 1000000000000 raw_interval`
  >> gvs []
  >> rpt strip_tac
  >> gvs []
  >> simp [registered_case10173_fs_gradient_row_exp_def]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_scale»
          [App «candle_cv_fs_scale» [];
           Uop Fst
             (from_cv
               (bounded_interval64_object_cv
                 (BoundedInterval64 b b0)))]) refs =
      (M_success (from_cv raw_lower),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [App «candle_cv_fs_scale» [];
              Uop Fst
                (from_cv
                  (bounded_interval64_object_cv
                    (BoundedInterval64 b b0)))]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [from_cv (Num 1000000000000);
              from_cv (bounded_signed64_object_cv b)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
           >> simp
                [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
                 compute_execTheory.from_cv_def,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> mp_tac
             (Q.INST
               [`factor` |-> `1000000000000`,
                `value` |-> `bounded_signed64_object_cv b`,
                `result` |-> `raw_lower`, `clock` |-> `clock`]
               compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_scale»
          [App «candle_cv_fs_scale» [];
           Uop Snd
             (from_cv
               (bounded_interval64_object_cv
                 (BoundedInterval64 b b0)))]) refs =
      (M_success (from_cv raw_upper),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [App «candle_cv_fs_scale» [];
              Uop Snd
                (from_cv
                  (bounded_interval64_object_cv
                    (BoundedInterval64 b b0)))]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [from_cv (Num 1000000000000);
              from_cv (bounded_signed64_object_cv b0)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
           >> simp
                [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
                 compute_execTheory.from_cv_def,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> mp_tac
             (Q.INST
               [`factor` |-> `1000000000000`,
                `value` |-> `bounded_signed64_object_cv b0`,
                `result` |-> `raw_upper`, `clock` |-> `clock`]
               compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_dot_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (bounded_interval64_object_cv_list row)]) refs =
      (M_success (from_cv variation),refs)` by
       (`8 * (LENGTH radii + 1) < clock` by intLib.ARITH_TAC
        >> mp_tac
             (Q.INST
               [`entries` |-> `row`, `clock` |-> `clock`,
                `refs` |-> `refs`, `result` |-> `variation`]
               compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_dot_abs_upper_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_neg»
          [App «candle_cv_fs_dot_abs_upper»
            [from_cv (registered_case10173_word64_object_cv_list radii);
             from_cv (bounded_interval64_object_cv_list row)]]) refs =
      (M_success (from_cv negative_variation),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_neg»
             [App «candle_cv_fs_dot_abs_upper»
               [from_cv
                  (registered_case10173_word64_object_cv_list radii);
                from_cv (bounded_interval64_object_cv_list row)]]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_neg» [from_cv variation]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> fs [])
        >> fs
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_eval])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_gradient_center_interval_exp
          (from_cv
            (bounded_interval64_object_cv
              (BoundedInterval64 b b0)))) refs =
      (M_success (from_cv (Pair raw_lower raw_upper)),refs)` by
       (simp [registered_case10173_fs_gradient_center_interval_exp_def]
        >> irule
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_gradient_variation_interval_exp
          (from_cv (registered_case10173_word64_object_cv_list radii))
          (from_cv (bounded_interval64_object_cv_list row))) refs =
      (M_success
        (from_cv (Pair negative_variation variation)),refs)` by
       (simp [registered_case10173_fs_gradient_variation_interval_exp_def]
        >> irule
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_gradient_raw_interval_exp
          (from_cv (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (bounded_interval64_object_cv
              (BoundedInterval64 b b0)))
          (from_cv (bounded_interval64_object_cv_list row))) refs =
      (M_success (from_cv raw_interval),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (registered_case10173_fs_gradient_raw_interval_exp
             (from_cv (registered_case10173_word64_object_cv_list radii))
             (from_cv
               (bounded_interval64_object_cv
                 (BoundedInterval64 b b0)))
             (from_cv (bounded_interval64_object_cv_list row))) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_interval_add»
             [Pair (from_cv raw_lower) (from_cv raw_upper);
              Pair (from_cv negative_variation)
                (from_cv variation)]) refs` by
          (simp
             [registered_case10173_fs_gradient_raw_interval_exp_def]
           >> mp_tac
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  (Q.INST
                    [`argument1` |->
                       `registered_case10173_fs_gradient_center_interval_exp
                          (from_cv
                            (bounded_interval64_object_cv
                              (BoundedInterval64 b b0)))`,
                     `argument2` |->
                       `registered_case10173_fs_gradient_variation_interval_exp
                          (from_cv
                            (registered_case10173_word64_object_cv_list
                              radii))
                          (from_cv
                            (bounded_interval64_object_cv_list row))`,
                     `result1` |-> `Pair raw_lower raw_upper`,
                     `result2` |-> `Pair negative_variation variation`,
                     `function_name` |-> `«candle_cv_fs_raw_interval_add»`,
                     `ceqs` |->
                       `registered_case10173_historical_chunk16_ceqs`,
                     `clock` |-> `clock`, `refs` |-> `refs`]
                    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results))
           >> simp [])
        >> mp_tac
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               (Q.INST
                 [`left` |-> `Pair raw_lower raw_upper`,
                  `right` |-> `Pair negative_variation variation`,
                  `result` |-> `raw_interval`, `clock` |-> `clock`]
                 registered_case10173_fs_raw_interval_add_eval))
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_gradient_row_exp
          (from_cv (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (bounded_interval64_object_cv
              (BoundedInterval64 b b0)))
          (from_cv (bounded_interval64_object_cv_list row))) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_round»
          [from_cv (Num 1000000000000);from_cv raw_interval]) refs` by
       (simp [registered_case10173_fs_gradient_row_exp_def]
        >> mp_tac
             (Q.INST
               [`argument1` |-> `App «candle_cv_fs_scale» []`,
                `argument2` |->
                  `registered_case10173_fs_gradient_raw_interval_exp
                     (from_cv
                       (registered_case10173_word64_object_cv_list radii))
                     (from_cv
                       (bounded_interval64_object_cv
                         (BoundedInterval64 b b0)))
                     (from_cv (bounded_interval64_object_cv_list row))`,
                `result1` |-> `Num 1000000000000`,
                `result2` |-> `raw_interval`,
                `function_name` |-> `«candle_cv_fs_raw_interval_round»`,
                `ceqs` |-> `registered_case10173_historical_chunk16_ceqs`,
                `clock` |-> `clock`, `refs` |-> `refs`]
               compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results)
        >> simp
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_round»
          [from_cv (Num 1000000000000);from_cv raw_interval]) refs =
      (M_success (from_cv result),refs)` by
       (mp_tac
          (Q.INST
            [`denominator` |-> `1000000000000`,
             `interval` |-> `raw_interval`, `result` |-> `result`,
             `clock` |-> `clock`]
            registered_case10173_fs_raw_interval_round_eval)
        >> simp [])
  >> fs [registered_case10173_fs_gradient_row_exp_def]
QED

val _ = export_theory ();
