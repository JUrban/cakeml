(*****************************************************************************
 * Exact evaluator semantics for the first reusable delta linear operations.
 *
 * These lemmas establish the production/object-q boundary without expanding
 * a genuine numerical result.  They are the first common layer for all three
 * authenticated 4*x_i*delta specializations.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaLinearEval
Ancestors
  compute_boundedCase16594ObjectMulEval
  compute_boundedAnalyticObjectDeltaLinearRefinement
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_scale4_body_def:
  bounded_case16594_object_delta_scale4_body =
    Let «twice»
      (App «candle_cv_q_interval_add» [Var «value»;Var «value»])
      (App «candle_cv_q_interval_add» [Var «twice»;Var «twice»])
End

Theorem bounded_case16594_object_delta_scale4_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_scale4» =
    SOME ([«value»],bounded_case16594_object_delta_scale4_body)
Proof
  rw [bounded_case16594_object_delta_scale4_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_scale4_eval:
  bounded_packed_q_interval_encoded value /\
  7 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_scale4» [from_cv value])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_object_q_interval_scale4_cv value)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_add_cv value value)` by
       (irule
          compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«value»,from_cv value)]
            bounded_case16594_object_delta_scale4_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_literal_app1
      >> simp []
      >> ACCEPT_TAC bounded_case16594_object_delta_scale4_lookup)
  >> simp
       [bounded_case16594_object_delta_scale4_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_object_q_interval_add_cv value value`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> rw
       [compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_scale4_cv_def]
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_product_center_value_body_def:
  bounded_case16594_object_delta_product_center_value_body =
    App «candle_cv_q_packed_delta_scale4»
      [App «candle_cv_q_interval_mul»
        [Var «coordinate_value»;Var «delta_value»]]
End

Theorem bounded_case16594_object_delta_product_center_value_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_center_value» =
    SOME
      ([«coordinate_value»;«delta_value»],
       bounded_case16594_object_delta_product_center_value_body)
Proof
  rw [bounded_case16594_object_delta_product_center_value_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_product_center_value_eval:
  bounded_packed_q_interval_encoded coordinate_value /\
  bounded_packed_q_interval_encoded delta_value /\
  9 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_center_value»
        [from_cv coordinate_value;from_cv delta_value]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_interval_scale4_cv
          (bounded_object_q_interval_mul_cv
            coordinate_value delta_value))),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_interval_mul_cv coordinate_value delta_value)` by
       (irule
          compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
        >> irule
             compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
        >> simp
             [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«coordinate_value»,from_cv coordinate_value);
             («delta_value»,from_cv delta_value)]
            bounded_case16594_object_delta_product_center_value_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
      >> simp []
      >> ACCEPT_TAC
           bounded_case16594_object_delta_product_center_value_lookup)
  >> simp
       [bounded_case16594_object_delta_product_center_value_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_scale4»
            [from_cv
              (bounded_object_q_interval_mul_cv
                coordinate_value delta_value)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> simp []
      >> irule
           compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_q_interval_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_delta_scale4_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
