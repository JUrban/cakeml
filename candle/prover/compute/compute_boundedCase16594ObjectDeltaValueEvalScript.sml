(*****************************************************************************
 * Exact evaluator semantics for the production compact delta value.
 *
 * The argument-result helpers keep expression evaluation separate from the
 * exact source list constructors and left-fold sum proved below.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaValueEval
Ancestors
  compute_boundedCase16594ObjectDeltaSumEval
  compute_boundedCase16594ObjectDeltaPrimitiveEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_packed_interval_neg_eval:
  bounded_packed_q_interval_encoded value /\
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg» [from_cv value]) (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_neg_cv value)),refs)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_neg_encoded_eval
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_delta_neg_packed_encoded:
  bounded_packed_q_interval_encoded value ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_neg_cv value)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_neg_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

Theorem bounded_case16594_object_delta_mul3_packed_encoded:
  bounded_packed_q_interval_encoded first_value /\
  bounded_packed_q_interval_encoded second_value /\
  bounded_packed_q_interval_encoded third_value ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_mul3_cv
      first_value second_value third_value)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> rw
       [compute_boundedAnalyticObjectDeltaProductRefinementTheory.bounded_object_q_interval_mul3_cv_def]
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded]
QED

Theorem bounded_case16594_object_delta_sum6_argument_results:
  EVERY bounded_packed_q_interval_encoded
    [value0;value1;value2;value3;value4;value5] /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression0 (refs:hol_refs) = (M_success (from_cv value0),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression1 refs = (M_success (from_cv value1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression2 refs = (M_success (from_cv value2),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression3 refs = (M_success (from_cv value3),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression4 refs = (M_success (from_cv value4),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression5 refs = (M_success (from_cv value5),refs) /\
  128 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum»
        [App «candle_cv_q_packed_delta_six»
          [expression0;expression1;expression2;expression3;expression4;
           expression5]]) refs =
    (M_success
      (from_cv
        (bounded_object_q_interval_sum_cv
          [value0;value1;value2;value3;value4;value5])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sum»
            [from_cv
              (bounded_object_q_cv_list
                [value0;value1;value2;value3;value4;value5])]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_delta_six»
                [from_cv value0;from_cv value1;from_cv value2;
                 from_cv value3;from_cv value4;from_cv value5]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
          >> simp [])
      >> irule
           compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_six_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_delta_sum7_argument_results:
  EVERY bounded_packed_q_interval_encoded
    [value0;value1;value2;value3;value4;value5;value6] /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression0 (refs:hol_refs) = (M_success (from_cv value0),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression1 refs = (M_success (from_cv value1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression2 refs = (M_success (from_cv value2),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression3 refs = (M_success (from_cv value3),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression4 refs = (M_success (from_cv value4),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression5 refs = (M_success (from_cv value5),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression6 refs = (M_success (from_cv value6),refs) /\
  128 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum»
        [App «candle_cv_q_packed_delta_seven»
          [expression0;expression1;expression2;expression3;expression4;
           expression5;expression6]]) refs =
    (M_success
      (from_cv
        (bounded_object_q_interval_sum_cv
          [value0;value1;value2;value3;value4;value5;value6])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sum»
            [from_cv
              (bounded_object_q_cv_list
                [value0;value1;value2;value3;value4;value5;value6])]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_delta_seven»
                [from_cv value0;from_cv value1;from_cv value2;
                 from_cv value3;from_cv value4;from_cv value5;
                 from_cv value6]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_app7_argument_results
          >> simp [])
      >> irule
           compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_seven_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_value_six_body_def:
  bounded_case16594_object_delta_value_six_body =
    Let «first_linear»
      (App «candle_cv_q_packed_delta_sum»
        [App «candle_cv_q_packed_delta_six»
          [App «candle_cv_q_interval_neg» [Var «x0»];Var «x1»;
           Var «x2»;App «candle_cv_q_interval_neg» [Var «x3»];
           Var «x4»;Var «x5»]])
      (Let «second_linear»
        (App «candle_cv_q_packed_delta_sum»
          [App «candle_cv_q_packed_delta_six»
            [Var «x0»;App «candle_cv_q_interval_neg» [Var «x1»];
             Var «x2»;Var «x3»;
             App «candle_cv_q_interval_neg» [Var «x4»];Var «x5»]])
        (Let «third_linear»
          (App «candle_cv_q_packed_delta_sum»
            [App «candle_cv_q_packed_delta_six»
              [Var «x0»;Var «x1»;
               App «candle_cv_q_interval_neg» [Var «x2»];Var «x3»;
               Var «x4»;App «candle_cv_q_interval_neg» [Var «x5»]]])
          (Let «first»
            (App «candle_cv_q_packed_delta_mul3»
              [Var «x0»;Var «x3»;Var «first_linear»])
            (Let «second»
              (App «candle_cv_q_packed_delta_mul3»
                [Var «x1»;Var «x4»;Var «second_linear»])
              (Let «third»
                (App «candle_cv_q_packed_delta_mul3»
                  [Var «x2»;Var «x5»;Var «third_linear»])
                (Let «fourth»
                  (App «candle_cv_q_packed_delta_mul3»
                    [Var «x1»;Var «x2»;Var «x3»])
                  (Let «fifth»
                    (App «candle_cv_q_packed_delta_mul3»
                      [Var «x0»;Var «x2»;Var «x4»])
                    (Let «sixth»
                      (App «candle_cv_q_packed_delta_mul3»
                        [Var «x0»;Var «x1»;Var «x5»])
                      (Let «seventh»
                        (App «candle_cv_q_packed_delta_mul3»
                          [Var «x3»;Var «x4»;Var «x5»])
                        (App «candle_cv_q_packed_delta_sum»
                          [App «candle_cv_q_packed_delta_seven»
                            [Var «first»;Var «second»;Var «third»;
                             App «candle_cv_q_interval_neg» [Var «fourth»];
                             App «candle_cv_q_interval_neg» [Var «fifth»];
                             App «candle_cv_q_interval_neg» [Var «sixth»];
                             App «candle_cv_q_interval_neg»
                               [Var «seventh»]]]))))))))))
End

Theorem bounded_case16594_object_delta_value_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_value_six» =
    SOME
      ([«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_value_six_body)
Proof
  rw [bounded_case16594_object_delta_value_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_value_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_value_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
         («x3»,from_cv x3);(«x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_value_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp []
  >> ACCEPT_TAC bounded_case16594_object_delta_value_six_lookup
QED

Theorem bounded_case16594_object_delta_value_six_eval:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  4096 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_value_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_delta_value_six_cv x0 x1 x2 x3 x4 x5)),refs)
Proof
  strip_tac
  >> fs []
  >> rw [bounded_case16594_object_delta_value_six_unfold]
  >> simp
       [bounded_case16594_object_delta_value_six_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv x0;x1;x2;
           bounded_object_q_interval_neg_cv x3;x4;x5]`
  >> conj_tac
  >- (irule bounded_case16594_object_delta_sum6_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_delta_neg_packed_encoded]
      >> rpt conj_tac
      >> TRY
           (irule bounded_case16594_object_delta_packed_interval_neg_eval
            >> simp []
            >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_sum_cv
          [x0;bounded_object_q_interval_neg_cv x1;x2;x3;
           bounded_object_q_interval_neg_cv x4;x5]`
  >> conj_tac
  >- (irule bounded_case16594_object_delta_sum6_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_delta_neg_packed_encoded]
      >> rpt conj_tac
      >> TRY
           (irule bounded_case16594_object_delta_packed_interval_neg_eval
            >> simp []
            >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_sum_cv
          [x0;x1;bounded_object_q_interval_neg_cv x2;x3;x4;
           bounded_object_q_interval_neg_cv x5]`
  >> conj_tac
  >- (irule bounded_case16594_object_delta_sum6_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_delta_neg_packed_encoded]
      >> rpt conj_tac
      >> TRY
           (irule bounded_case16594_object_delta_packed_interval_neg_eval
            >> simp []
            >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_mul3_cv x0 x3
          (bounded_object_q_interval_sum_cv
            [bounded_object_q_interval_neg_cv x0;x1;x2;
             bounded_object_q_interval_neg_cv x3;x4;x5])`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp
           [compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded,
            bounded_case16594_object_delta_neg_packed_encoded]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_mul3_cv x1 x4
          (bounded_object_q_interval_sum_cv
            [x0;bounded_object_q_interval_neg_cv x1;x2;x3;
             bounded_object_q_interval_neg_cv x4;x5])`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp
           [compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded,
            bounded_case16594_object_delta_neg_packed_encoded]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_mul3_cv x2 x5
          (bounded_object_q_interval_sum_cv
            [x0;x1;bounded_object_q_interval_neg_cv x2;x3;x4;
             bounded_object_q_interval_neg_cv x5])`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp
           [compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded,
            bounded_case16594_object_delta_neg_packed_encoded]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_interval_mul3_cv x1 x2 x3`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_interval_mul3_cv x0 x2 x4`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_interval_mul3_cv x0 x1 x5`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_interval_mul3_cv x3 x4 x5`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_mul3_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> rw
       [compute_boundedAnalyticObjectDeltaValueRefinementTheory.bounded_object_q_delta_value_six_cv_def]
  >> irule bounded_case16594_object_delta_sum7_argument_results
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        bounded_case16594_object_delta_mul3_packed_encoded,
        bounded_case16594_object_delta_neg_packed_encoded,
        compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded]
  >> rpt conj_tac
  >> TRY
       (irule bounded_case16594_object_delta_packed_interval_neg_eval
        >> simp
             [bounded_case16594_object_delta_mul3_packed_encoded]
        >> intLib.ARITH_TAC)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
