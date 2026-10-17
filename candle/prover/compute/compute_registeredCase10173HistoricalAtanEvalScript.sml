(*****************************************************************************
 * Registered evaluator semantics for the historical arctangent polynomial.
 *
 * The argument-result lemmas keep the literal nested source expressions
 * intact while reusing the already proved bounded interval operations.  The
 * two body definitions below are exact copies of the registered source.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalAtanEval
Ancestors
  compute_registeredCase10173HistoricalAtanConstantEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_interval_add_argument_results:
  bounded_object_fs_interval_add left right = SOME result /\
  4 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv left),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success (from_cv right),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [left_expression;right_expression]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_add»
          [left_expression;right_expression]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_interval_add»
          [from_cv left;from_cv right]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_interval_mul_argument_results:
  bounded_object_fs_interval_mul_decimal left right = SOME result /\
  11 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      left_expression (refs:hol_refs) =
    (M_success (from_cv left),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      right_expression refs =
    (M_success (from_cv right),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [left_expression;right_expression]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_interval_mul»
          [left_expression;right_expression]) refs =
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_angle_interval_mul»
          [from_cv left;from_cv right]) refs` by
       (irule
          compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
        >> simp [])
  >> rw []
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
  >> simp []
QED

Theorem registered_case10173_fs_interval_mul_add_argument_results:
  bounded_object_fs_interval_mul_add_decimal scalar accumulator addend =
      SOME result /\
  11 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      scalar_expression (refs:hol_refs) =
    (M_success (from_cv scalar),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      accumulator_expression refs =
    (M_success (from_cv accumulator),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      addend_expression refs =
    (M_success (from_cv addend),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [addend_expression;
         App «candle_cv_fs_angle_interval_mul»
           [scalar_expression;accumulator_expression]]) refs =
    (M_success (from_cv result),refs)
Proof
  rw
    [compute_boundedObjectHistoricalFirstDecimalTheory.bounded_object_fs_interval_mul_add_decimal_def]
  >> Cases_on `bounded_object_fs_interval_mul_decimal scalar accumulator`
  >> gvs []
  >> gvs []
  >> irule registered_case10173_fs_interval_add_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `addend`
  >> qexists_tac `x`
  >> simp []
  >> irule registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `scalar`
  >> qexists_tac `accumulator`
  >> simp []
QED

Definition registered_case10173_fs_hist_atan_pos_lower_body_def:
  registered_case10173_fs_hist_atan_pos_lower_body =
    Let «point» (App «candle_cv_fs_hist_point» [Var «x»])
      (Let «x2»
        (App «candle_cv_fs_angle_interval_mul»
          [Var «point»;Var «point»])
        (Let «polynomial»
          (App «candle_cv_fs_hist_rational_constant»
            [Num 0;Num 1;Num 11])
          (Let «polynomial»
            (App «candle_cv_fs_interval_add»
              [App «candle_cv_fs_hist_rational_constant»
                 [Num 1;Num 0;Num 9];
               App «candle_cv_fs_angle_interval_mul»
                 [Var «x2»;Var «polynomial»]])
            (Let «polynomial»
              (App «candle_cv_fs_interval_add»
                [App «candle_cv_fs_hist_rational_constant»
                   [Num 0;Num 1;Num 7];
                 App «candle_cv_fs_angle_interval_mul»
                   [Var «x2»;Var «polynomial»]])
              (Let «polynomial»
                (App «candle_cv_fs_interval_add»
                  [App «candle_cv_fs_hist_rational_constant»
                     [Num 1;Num 0;Num 5];
                   App «candle_cv_fs_angle_interval_mul»
                     [Var «x2»;Var «polynomial»]])
                (Let «polynomial»
                  (App «candle_cv_fs_interval_add»
                    [App «candle_cv_fs_hist_rational_constant»
                       [Num 0;Num 1;Num 3];
                     App «candle_cv_fs_angle_interval_mul»
                       [Var «x2»;Var «polynomial»]])
                  (App «candle_cv_fs_angle_interval_mul»
                    [Var «point»;
                     App «candle_cv_fs_interval_add»
                       [App «candle_cv_fs_interval_one» [];
                        App «candle_cv_fs_angle_interval_mul»
                          [Var «x2»;Var «polynomial»]]])))))))
End

Definition registered_case10173_fs_hist_atan_pos_upper_body_def:
  registered_case10173_fs_hist_atan_pos_upper_body =
    Let «point» (App «candle_cv_fs_hist_point» [Var «x»])
      (Let «x2»
        (App «candle_cv_fs_angle_interval_mul»
          [Var «point»;Var «point»])
        (Let «polynomial»
          (App «candle_cv_fs_hist_rational_constant»
            [Num 1;Num 0;Num 13])
          (Let «polynomial»
            (App «candle_cv_fs_interval_add»
              [App «candle_cv_fs_hist_rational_constant»
                 [Num 0;Num 1;Num 11];
               App «candle_cv_fs_angle_interval_mul»
                 [Var «x2»;Var «polynomial»]])
            (Let «polynomial»
              (App «candle_cv_fs_interval_add»
                [App «candle_cv_fs_hist_rational_constant»
                   [Num 1;Num 0;Num 9];
                 App «candle_cv_fs_angle_interval_mul»
                   [Var «x2»;Var «polynomial»]])
              (Let «polynomial»
                (App «candle_cv_fs_interval_add»
                  [App «candle_cv_fs_hist_rational_constant»
                     [Num 0;Num 1;Num 7];
                   App «candle_cv_fs_angle_interval_mul»
                     [Var «x2»;Var «polynomial»]])
                (Let «polynomial»
                  (App «candle_cv_fs_interval_add»
                    [App «candle_cv_fs_hist_rational_constant»
                       [Num 1;Num 0;Num 5];
                     App «candle_cv_fs_angle_interval_mul»
                       [Var «x2»;Var «polynomial»]])
                  (Let «polynomial»
                    (App «candle_cv_fs_interval_add»
                      [App «candle_cv_fs_hist_rational_constant»
                         [Num 0;Num 1;Num 3];
                       App «candle_cv_fs_angle_interval_mul»
                         [Var «x2»;Var «polynomial»]])
                    (App «candle_cv_fs_angle_interval_mul»
                      [Var «point»;
                       App «candle_cv_fs_interval_add»
                         [App «candle_cv_fs_interval_one» [];
                          App «candle_cv_fs_angle_interval_mul»
                            [Var «x2»;Var «polynomial»]]]))))))))
End

Theorem registered_case10173_fs_hist_atan_pos_lower_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_atan_pos_lower» =
    SOME ([«x»],registered_case10173_fs_hist_atan_pos_lower_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_atan_pos_upper_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_atan_pos_upper» =
    SOME ([«x»],registered_case10173_fs_hist_atan_pos_upper_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_atan_pos_lower_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_pos_lower» [from_cv input])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv input)]
        registered_case10173_fs_hist_atan_pos_lower_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_atan_pos_lower_lookup]
QED

Theorem registered_case10173_fs_hist_atan_pos_upper_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_pos_upper» [from_cv input])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«x»,from_cv input)]
        registered_case10173_fs_hist_atan_pos_upper_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_hist_atan_pos_upper_lookup]
QED

Definition registered_case10173_hist_positive_endpoint_object_def:
  registered_case10173_hist_positive_endpoint_object magnitude =
    bounded_signed64_object_cv (BoundedSigned64 F magnitude)
End

Definition registered_case10173_hist_positive_point_object_def:
  registered_case10173_hist_positive_point_object magnitude =
    bounded_interval64_object_cv
      (BoundedInterval64
        (BoundedSigned64 F magnitude)
        (BoundedSigned64 F magnitude))
End

Theorem registered_case10173_fs_hist_atan_pos_lower_trace_eval:
  bounded_object_fs_interval_mul_decimal
      (registered_case10173_hist_positive_point_object magnitude)
      (registered_case10173_hist_positive_point_object magnitude) =
    SOME square /\
  bounded_object_fs_interval_mul_add_decimal square
      (bounded_interval64_object_cv bounded_atan_neg_eleventh_decimal)
      (bounded_interval64_object_cv bounded_atan_pos_ninth_decimal) =
    SOME step9 /\
  bounded_object_fs_interval_mul_add_decimal square step9
      (bounded_interval64_object_cv bounded_atan_neg_seventh_decimal) =
    SOME step7 /\
  bounded_object_fs_interval_mul_add_decimal square step7
      (bounded_interval64_object_cv bounded_atan_pos_fifth_decimal) =
    SOME step5 /\
  bounded_object_fs_interval_mul_add_decimal square step5
      (bounded_interval64_object_cv bounded_atan_neg_third_decimal) =
    SOME step3 /\
  bounded_object_fs_interval_mul_add_decimal square step3
      (bounded_interval64_object_cv bounded_atan_one_decimal) =
    SOME body /\
  bounded_object_fs_interval_mul_decimal
      (registered_case10173_hist_positive_point_object magnitude) body =
    SOME result /\
  24 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_atan_pos_lower»
        [from_cv
          (registered_case10173_hist_positive_endpoint_object magnitude)])
      (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_atan_pos_lower_unfold]
  >> simp
       [registered_case10173_fs_hist_atan_pos_lower_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv (registered_case10173_hist_positive_point_object magnitude)`
  >> conj_tac
  >- (simp
       [registered_case10173_hist_positive_endpoint_object_def,
        registered_case10173_hist_positive_point_object_def]
      >> irule
           compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_point_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv square`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv
            bounded_atan_neg_eleventh_decimal)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_fs_hist_rational_neg_eleventh_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv step9`
  >> conj_tac
  >- (irule
        (Q.INST
          [`scalar` |-> `square`,
           `accumulator` |->
             `bounded_interval64_object_cv
                bounded_atan_neg_eleventh_decimal`,
           `addend` |->
             `bounded_interval64_object_cv bounded_atan_pos_ninth_decimal`,
           `result` |-> `step9`]
          registered_case10173_fs_interval_mul_add_argument_results)
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_fs_hist_rational_pos_ninth_eval]
      >> qexists_tac `square`
      >> simp
           [compute_execProofTheory.subst_from_cv,
            compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv step7`
  >> conj_tac
  >- (irule
        (Q.INST
          [`scalar` |-> `square`, `accumulator` |-> `step9`,
           `addend` |->
             `bounded_interval64_object_cv bounded_atan_neg_seventh_decimal`,
           `result` |-> `step7`]
          registered_case10173_fs_interval_mul_add_argument_results)
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_fs_hist_rational_neg_seventh_eval]
      >> qexists_tac `square`
      >> qexists_tac `step9`
      >> simp
           [compute_execProofTheory.subst_from_cv,
            compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv step5`
  >> conj_tac
  >- (irule
        (Q.INST
          [`scalar` |-> `square`, `accumulator` |-> `step7`,
           `addend` |->
             `bounded_interval64_object_cv bounded_atan_pos_fifth_decimal`,
           `result` |-> `step5`]
          registered_case10173_fs_interval_mul_add_argument_results)
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_fs_hist_rational_pos_fifth_eval]
      >> qexists_tac `square`
      >> qexists_tac `step7`
      >> simp
           [compute_execProofTheory.subst_from_cv,
            compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv step3`
  >> conj_tac
  >- (irule
        (Q.INST
          [`scalar` |-> `square`, `accumulator` |-> `step5`,
           `addend` |->
             `bounded_interval64_object_cv bounded_atan_neg_third_decimal`,
           `result` |-> `step3`]
          registered_case10173_fs_interval_mul_add_argument_results)
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_registeredCase10173HistoricalAtanConstantEvalTheory.registered_case10173_fs_hist_rational_neg_third_eval]
      >> qexists_tac `square`
      >> qexists_tac `step5`
      >> simp
           [compute_execProofTheory.subst_from_cv,
            compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_evalTheory.subst_def]
  >> irule registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `registered_case10173_hist_positive_point_object magnitude`
  >> qexists_tac `body`
  >> simp
       [compute_execProofTheory.subst_from_cv,
        compute_execProofTheory.compute_eval_from_cv]
  >> irule
       (Q.INST
         [`scalar` |-> `square`, `accumulator` |-> `step3`,
          `addend` |->
            `bounded_interval64_object_cv bounded_atan_one_decimal`,
          `result` |-> `body`]
         registered_case10173_fs_interval_mul_add_argument_results)
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> conj_tac
  >- (mp_tac
       (Q.INST [`clock` |-> `clock - 8`, `refs` |-> `refs`]
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_interval_one_eval)
      >> simp
           [compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def,
            compute_boundedObjectIntervalRelationTheory.bounded_interval64_object_cv_def,
            compute_boundedObjectIntervalRelationTheory.bounded_signed64_object_cv_def]
      >> intLib.ARITH_TAC)
  >> qexists_tac `square`
  >> qexists_tac `step3`
  >> simp []
QED

val _ = export_theory ();
