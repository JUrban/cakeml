(*****************************************************************************
 * Registered evaluator refinement for the fixed-scale Taylor value bound.
 *
 * The first layer below proves the complete linear-plus-quadratic error
 * calculation.  It is then used by the rounded value enclosure and result
 * completion wrapper.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorValueEval
Ancestors
  compute_registeredCase10173TaylorGradientRowsEval
  compute_registeredCase10173TaylorCompletionEval
Libs
  bossLib preamble

Definition registered_case10173_fs_two_scale_exp_def:
  registered_case10173_fs_two_scale_exp =
    Binop Mul (Num 2) (App «candle_cv_fs_scale» [])
End

Definition registered_case10173_fs_taylor_error_exp_def:
  registered_case10173_fs_taylor_error_exp radii gradient hessian_rows =
    App «candle_cv_fs_raw_add»
      [App «candle_cv_fs_raw_scale»
        [registered_case10173_fs_two_scale_exp;
         App «candle_cv_fs_dot_abs_upper» [radii;gradient]];
       App «candle_cv_fs_weighted_rows_abs_upper»
         [radii;radii;hessian_rows]]
End

Theorem registered_case10173_compute_eval_binop_mul_num_results:
  compute_eval clock ceqs left (refs:hol_refs) =
      (M_success (Num left_value),refs) /\
  compute_eval clock ceqs right refs =
      (M_success (Num right_value),refs) ==>
  compute_eval clock ceqs (Binop Mul left right) refs =
    (M_success (Num (left_value * right_value)),refs)
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_arith_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_two_scale_exp_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      registered_case10173_fs_two_scale_exp (refs:hol_refs) =
    (M_success (from_cv (Num 2000000000000)),refs)
Proof
  strip_tac
  >> simp
    [registered_case10173_fs_two_scale_exp_def,
     compute_execTheory.from_cv_def]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (Num 2) refs = (M_success (Num 2),refs)` by
       (mp_tac
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`x` |-> `(Num 2:cv)`, `s` |-> `refs`,
             `ck` |-> `clock`,
             `eqs` |-> `registered_case10173_historical_chunk16_ceqs`]
             (SPEC_ALL compute_execProofTheory.compute_eval_from_cv)))
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_scale» []) refs =
      (M_success (Num 1000000000000),refs)` by
       simp
         [compute_execTheory.from_cv_def,
          compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_scale_eval]
  >> mp_tac
       (Q.INST
         [`left` |-> `Num 2`,
          `right` |-> `App «candle_cv_fs_scale» []`,
          `left_value` |-> `2`, `right_value` |-> `1000000000000`,
          `clock` |-> `clock`,
          `ceqs` |-> `registered_case10173_historical_chunk16_ceqs`,
          `refs` |-> `refs`]
         registered_case10173_compute_eval_binop_mul_num_results)
  >> simp []
QED

Theorem registered_case10173_fs_taylor_error_object_eval:
  bounded_object_fs_taylor_error radii gradient rows = SOME result /\
  64 * (2 * LENGTH radii + LENGTH rows + 2) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_taylor_error_exp
        (from_cv (registered_case10173_word64_object_cv_list radii))
        (from_cv (bounded_interval64_object_cv_list gradient))
        (from_cv (bounded_interval64_object_cv_matrix rows)))
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw
    [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_error_def]
  >> Cases_on `bounded_object_fs_dot_abs_upper radii gradient`
  >> gvs []
  >> Cases_on `bounded_object_fs_raw_scale 2000000000000 x`
  >> gvs []
  >> Cases_on
       `bounded_object_fs_weighted_rows_abs_upper radii radii rows`
  >> gvs []
  >> Cases_on `bounded_object_fs_raw_add x' x''`
  >> gvs []
  >> simp [registered_case10173_fs_taylor_error_exp_def]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_dot_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (bounded_interval64_object_cv_list gradient)]) refs =
      (M_success (from_cv x),refs)` by
       (`8 * (LENGTH radii + 1) < clock` by intLib.ARITH_TAC
        >> mp_tac
             (Q.INST
               [`entries` |-> `gradient`, `clock` |-> `clock`,
                `refs` |-> `refs`, `result` |-> `x`]
               compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_fs_dot_abs_upper_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_scale»
          [registered_case10173_fs_two_scale_exp;
           App «candle_cv_fs_dot_abs_upper»
             [from_cv
                (registered_case10173_word64_object_cv_list radii);
              from_cv
                (bounded_interval64_object_cv_list gradient)]]) refs =
      (M_success (from_cv x'),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [registered_case10173_fs_two_scale_exp;
              App «candle_cv_fs_dot_abs_upper»
                [from_cv
                   (registered_case10173_word64_object_cv_list radii);
                 from_cv
                   (bounded_interval64_object_cv_list gradient)]]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [from_cv (Num 2000000000000);from_cv x]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> simp [registered_case10173_fs_two_scale_exp_eval])
        >> mp_tac
             (Q.INST
               [`factor` |-> `2000000000000`, `value` |-> `x`,
                `result` |-> `x'`, `clock` |-> `clock`]
               compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_weighted_rows_abs_upper»
          [from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (registered_case10173_word64_object_cv_list radii);
           from_cv (bounded_interval64_object_cv_matrix rows)]) refs =
      (M_success (from_cv x''),refs)` by
       (`16 * (LENGTH radii + LENGTH radii + 2) < clock` by
          intLib.ARITH_TAC
        >> mp_tac
             (Q.INST
               [`weights` |-> `radii`, `rows` |-> `rows`,
                `clock` |-> `clock`, `refs` |-> `refs`,
                `result` |-> `x''`]
               compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_fs_weighted_rows_abs_upper_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add»
          [App «candle_cv_fs_raw_scale»
            [registered_case10173_fs_two_scale_exp;
             App «candle_cv_fs_dot_abs_upper»
               [from_cv
                  (registered_case10173_word64_object_cv_list radii);
                from_cv
                  (bounded_interval64_object_cv_list gradient)]];
           App «candle_cv_fs_weighted_rows_abs_upper»
             [from_cv
                (registered_case10173_word64_object_cv_list radii);
              from_cv
                (registered_case10173_word64_object_cv_list radii);
              from_cv
                (bounded_interval64_object_cv_matrix rows)]]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_add» [from_cv x';from_cv x'']) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp []
        >> intLib.ARITH_TAC)
  >> fs
       [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_add_eval]
QED

Definition registered_case10173_fs_value_center_interval_exp_def:
  registered_case10173_fs_value_center_interval_exp center_value =
    Pair
      (App «candle_cv_fs_raw_scale»
        [App «candle_cv_fs_two_scale_squared» [];Uop Fst center_value])
      (App «candle_cv_fs_raw_scale»
        [App «candle_cv_fs_two_scale_squared» [];Uop Snd center_value])
End

Definition registered_case10173_fs_value_error_interval_exp_def:
  registered_case10173_fs_value_error_interval_exp
      radii center_gradient hessian_rows =
    Pair
      (App «candle_cv_fs_raw_neg»
        [registered_case10173_fs_taylor_error_exp
          radii center_gradient hessian_rows])
      (registered_case10173_fs_taylor_error_exp
        radii center_gradient hessian_rows)
End

Definition registered_case10173_fs_value_raw_interval_exp_def:
  registered_case10173_fs_value_raw_interval_exp
      radii center_value center_gradient hessian_rows =
    App «candle_cv_fs_raw_interval_add»
      [registered_case10173_fs_value_center_interval_exp center_value;
       registered_case10173_fs_value_error_interval_exp
         radii center_gradient hessian_rows]
End

Definition registered_case10173_fs_taylor_value_exp_def:
  registered_case10173_fs_taylor_value_exp
      radii center_value center_gradient hessian_rows =
    App «candle_cv_fs_raw_interval_round»
      [App «candle_cv_fs_two_scale_squared» [];
       registered_case10173_fs_value_raw_interval_exp
         radii center_value center_gradient hessian_rows]
End

Theorem registered_case10173_fs_taylor_value_object_eval:
  bounded_object_fs_taylor_value_complete
      radii center_value center_gradient rows = SOME result /\
  128 * (2 * LENGTH radii + LENGTH rows + 2) < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_taylor_value_exp
        (from_cv (registered_case10173_word64_object_cv_list radii))
        (from_cv (bounded_interval64_object_cv center_value))
        (from_cv (bounded_interval64_object_cv_list center_gradient))
        (from_cv (bounded_interval64_object_cv_matrix rows)))
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  Cases_on `center_value`
  >> rw
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_value_complete_def]
  >> Cases_on `bounded_object_fs_taylor_error radii center_gradient rows`
  >> gvs []
  >> rename1
       `bounded_object_fs_taylor_error radii center_gradient rows =
          SOME object_error`
  >> Cases_on
       `bounded_object_fs_raw_scale 2000000000000000000000000
          (bounded_signed64_object_cv b)`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_scale 2000000000000000000000000
          (bounded_signed64_object_cv b) = SOME scaled_lower`
  >> Cases_on
       `bounded_object_fs_raw_scale 2000000000000000000000000
          (bounded_signed64_object_cv b0)`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_scale 2000000000000000000000000
          (bounded_signed64_object_cv b0) = SOME scaled_upper`
  >> Cases_on `bounded_object_fs_raw_neg object_error`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_neg object_error = SOME negative_error`
  >> Cases_on
       `bounded_object_fs_raw_interval_add
          (Pair scaled_lower scaled_upper)
          (Pair negative_error object_error)`
  >> gvs []
  >> rename1
       `bounded_object_fs_raw_interval_add
          (Pair scaled_lower scaled_upper)
          (Pair negative_error object_error) = SOME raw_interval`
  >> Cases_on
       `bounded_object_fs_raw_interval_round
          2000000000000000000000000 raw_interval`
  >> gvs []
  >> simp [registered_case10173_fs_taylor_value_exp_def]
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_taylor_error_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (bounded_interval64_object_cv_list center_gradient))
          (from_cv
            (bounded_interval64_object_cv_matrix rows))) refs =
      (M_success (from_cv object_error),refs)` by
       (`64 * (2 * LENGTH radii + LENGTH rows + 2) < clock` by
          intLib.ARITH_TAC
        >> mp_tac
             (Q.INST
               [`gradient` |-> `center_gradient`, `rows` |-> `rows`,
                `result` |-> `object_error`, `clock` |-> `clock`,
                `refs` |-> `refs`]
               registered_case10173_fs_taylor_error_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_scale»
          [App «candle_cv_fs_two_scale_squared» [];
           Uop Fst
             (from_cv
               (bounded_interval64_object_cv
                 (BoundedInterval64 b b0)))]) refs =
      (M_success (from_cv scaled_lower),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [App «candle_cv_fs_two_scale_squared» [];
              Uop Fst
                (from_cv
                  (bounded_interval64_object_cv
                    (BoundedInterval64 b b0)))]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [from_cv (Num 2000000000000000000000000);
              from_cv (bounded_signed64_object_cv b)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_two_scale_squared_eval]
           >> simp
                [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
                 compute_execTheory.from_cv_def,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components])
        >> mp_tac
             (Q.INST
               [`factor` |-> `2000000000000000000000000`,
                `value` |-> `bounded_signed64_object_cv b`,
                `result` |-> `scaled_lower`, `clock` |-> `clock`]
               compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_scale»
          [App «candle_cv_fs_two_scale_squared» [];
           Uop Snd
             (from_cv
               (bounded_interval64_object_cv
                 (BoundedInterval64 b b0)))]) refs =
      (M_success (from_cv scaled_upper),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [App «candle_cv_fs_two_scale_squared» [];
              Uop Snd
                (from_cv
                  (bounded_interval64_object_cv
                    (BoundedInterval64 b b0)))]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_scale»
             [from_cv (Num 2000000000000000000000000);
              from_cv (bounded_signed64_object_cv b0)]) refs` by
          (irule
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
           >> conj_tac >- intLib.ARITH_TAC
           >> conj_tac
           >- simp
                [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_two_scale_squared_eval]
           >> simp
                [compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
                 compute_execTheory.from_cv_def,
                 compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components])
        >> mp_tac
             (Q.INST
               [`factor` |-> `2000000000000000000000000`,
                `value` |-> `bounded_signed64_object_cv b0`,
                `result` |-> `scaled_upper`, `clock` |-> `clock`]
               compute_registeredCase10173TaylorOrderEvalTheory.registered_case10173_fs_raw_scale_object_eval)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_neg»
          [registered_case10173_fs_taylor_error_exp
            (from_cv
              (registered_case10173_word64_object_cv_list radii))
            (from_cv
              (bounded_interval64_object_cv_list center_gradient))
            (from_cv
              (bounded_interval64_object_cv_matrix rows))]) refs =
      (M_success (from_cv negative_error),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_neg»
             [registered_case10173_fs_taylor_error_exp
               (from_cv
                 (registered_case10173_word64_object_cv_list radii))
               (from_cv
                 (bounded_interval64_object_cv_list center_gradient))
               (from_cv
                 (bounded_interval64_object_cv_matrix rows))]) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_neg»
             [from_cv object_error]) refs` by
          (irule
             compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
           >> conj_tac >- intLib.ARITH_TAC
           >> fs [])
        >> fs
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_raw_neg_eval])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_value_center_interval_exp
          (from_cv
            (bounded_interval64_object_cv
              (BoundedInterval64 b b0)))) refs =
      (M_success
        (from_cv (Pair scaled_lower scaled_upper)),refs)` by
       (simp
          [registered_case10173_fs_value_center_interval_exp_def]
        >> irule
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_value_error_interval_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (bounded_interval64_object_cv_list center_gradient))
          (from_cv
            (bounded_interval64_object_cv_matrix rows))) refs =
      (M_success
        (from_cv (Pair negative_error object_error)),refs)` by
       (simp
          [registered_case10173_fs_value_error_interval_exp_def]
        >> irule
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_value_raw_interval_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (bounded_interval64_object_cv
              (BoundedInterval64 b b0)))
          (from_cv
            (bounded_interval64_object_cv_list center_gradient))
          (from_cv
            (bounded_interval64_object_cv_matrix rows))) refs =
      (M_success (from_cv raw_interval),refs)` by
       (`compute_eval clock registered_case10173_historical_chunk16_ceqs
           (registered_case10173_fs_value_raw_interval_exp
             (from_cv
               (registered_case10173_word64_object_cv_list radii))
             (from_cv
               (bounded_interval64_object_cv
                 (BoundedInterval64 b b0)))
             (from_cv
               (bounded_interval64_object_cv_list center_gradient))
             (from_cv
               (bounded_interval64_object_cv_matrix rows))) refs =
         compute_eval clock registered_case10173_historical_chunk16_ceqs
           (App «candle_cv_fs_raw_interval_add»
             [Pair (from_cv scaled_lower) (from_cv scaled_upper);
              Pair (from_cv negative_error)
                (from_cv object_error)]) refs` by
          (simp [registered_case10173_fs_value_raw_interval_exp_def]
           >> mp_tac
                (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                  (Q.INST
                    [`argument1` |->
                       `registered_case10173_fs_value_center_interval_exp
                          (from_cv
                            (bounded_interval64_object_cv
                              (BoundedInterval64 b b0)))`,
                     `argument2` |->
                       `registered_case10173_fs_value_error_interval_exp
                          (from_cv
                            (registered_case10173_word64_object_cv_list
                              radii))
                          (from_cv
                            (bounded_interval64_object_cv_list
                              center_gradient))
                          (from_cv
                            (bounded_interval64_object_cv_matrix rows))`,
                     `result1` |-> `Pair scaled_lower scaled_upper`,
                     `result2` |-> `Pair negative_error object_error`,
                     `function_name` |-> `«candle_cv_fs_raw_interval_add»`,
                     `ceqs` |->
                       `registered_case10173_historical_chunk16_ceqs`,
                     `clock` |-> `clock`, `refs` |-> `refs`]
                    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results))
           >> simp [])
        >> mp_tac
             (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
               (Q.INST
                 [`left` |-> `Pair scaled_lower scaled_upper`,
                  `right` |-> `Pair negative_error object_error`,
                  `result` |-> `raw_interval`, `clock` |-> `clock`]
                 compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_add_eval))
        >> simp [])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (registered_case10173_fs_taylor_value_exp
          (from_cv
            (registered_case10173_word64_object_cv_list radii))
          (from_cv
            (bounded_interval64_object_cv
              (BoundedInterval64 b b0)))
          (from_cv
            (bounded_interval64_object_cv_list center_gradient))
          (from_cv
            (bounded_interval64_object_cv_matrix rows))) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_round»
          [from_cv (Num 2000000000000000000000000);
           from_cv raw_interval]) refs` by
       (simp [registered_case10173_fs_taylor_value_exp_def]
        >> mp_tac
             (Q.INST
               [`argument1` |->
                  `App «candle_cv_fs_two_scale_squared» []`,
                `argument2` |->
                  `registered_case10173_fs_value_raw_interval_exp
                     (from_cv
                       (registered_case10173_word64_object_cv_list radii))
                     (from_cv
                       (bounded_interval64_object_cv
                         (BoundedInterval64 b b0)))
                     (from_cv
                       (bounded_interval64_object_cv_list
                         center_gradient))
                     (from_cv
                       (bounded_interval64_object_cv_matrix rows))`,
                `result1` |-> `Num 2000000000000000000000000`,
                `result2` |-> `raw_interval`,
                `function_name` |->
                  `«candle_cv_fs_raw_interval_round»`,
                `ceqs` |->
                  `registered_case10173_historical_chunk16_ceqs`,
                `clock` |-> `clock`, `refs` |-> `refs`]
               compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results)
        >> simp
             [compute_registeredCase10173TaylorPrimitiveEvalTheory.registered_case10173_fs_two_scale_squared_eval])
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_raw_interval_round»
          [from_cv (Num 2000000000000000000000000);
           from_cv raw_interval]) refs =
      (M_success (from_cv result),refs)` by
       (mp_tac
          (Q.INST
            [`denominator` |-> `2000000000000000000000000`,
             `interval` |-> `raw_interval`, `result` |-> `result`,
             `clock` |-> `clock`]
            compute_registeredCase10173TaylorRoundEvalTheory.registered_case10173_fs_raw_interval_round_eval)
        >> simp [])
  >> fs [registered_case10173_fs_taylor_value_exp_def]
QED

val _ = export_theory ();
