(*****************************************************************************
 * Complete evaluator theorem for the production compact delta Hessian.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaHessianSixEval
Ancestors
  compute_boundedCase16594ObjectDeltaHessianCompleteEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_hessian_six_body_def:
  bounded_case16594_object_delta_hessian_six_body =
    App «candle_cv_q_packed_delta_sums»
      [App «candle_cv_q_packed_delta_hessian_rows_six»
        [Var «x0»;Var «x1»;Var «x2»;Var «x3»;Var «x4»;Var «x5»]]
End

Theorem bounded_case16594_object_delta_hessian_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_hessian_six» =
    SOME
      ([«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_hessian_six_body)
Proof
  rw [bounded_case16594_object_delta_hessian_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_hessian_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_hessian_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
         («x3»,from_cv x3);(«x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_hessian_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp []
  >> ACCEPT_TAC bounded_case16594_object_delta_hessian_six_lookup
QED

Theorem bounded_case16594_object_delta_hessian_six_eval:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  131072 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_hessian_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_object_q_delta_hessian_six_cv
            x0 x1 x2 x3 x4 x5))),refs)
Proof
  strip_tac
  >> fs []
  >> rewrite_tac
       [GSYM compute_boundedCase16594ObjectDeltaHessianEvalTheory.bounded_case16594_object_delta_hessian_rows_sums]
  >> rw [bounded_case16594_object_delta_hessian_six_unfold]
  >> simp
       [bounded_case16594_object_delta_hessian_six_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sums»
            [from_cv
              (bounded_object_q_cv_list
                (MAP bounded_object_q_cv_list
                  (bounded_case16594_object_delta_hessian_rows_six_cv
                    x0 x1 x2 x3 x4 x5)))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule bounded_case16594_object_delta_hessian_rows_six_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> MATCH_MP_TAC
       (Q.SPECL
         [`bounded_case16594_object_delta_hessian_rows_six_cv
             x0 x1 x2 x3 x4 x5`,`clock - 1`,`refs`]
         compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_delta_sums_eval)
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaHessianEvalTheory.bounded_case16594_object_delta_hessian_rows_encoded
      >> simp [])
  >> simp
       [compute_boundedCase16594ObjectDeltaHessianEvalTheory.bounded_case16594_object_delta_hessian_rows_six_cv_def]
QED

val _ = export_theory ();
