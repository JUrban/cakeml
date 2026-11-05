(*****************************************************************************
 * Exact source and object semantics for the compact 21-row delta Hessian.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaHessianEval
Ancestors
  compute_boundedCase16594ObjectDeltaHessianSumsEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_delta_hessian_rows_six_cv_def:
  bounded_case16594_object_delta_hessian_rows_six_cv x0 x1 x2 x3 x4 x5 =
    let n0 = bounded_object_q_interval_neg_cv x0;
        n1 = bounded_object_q_interval_neg_cv x1;
        n2 = bounded_object_q_interval_neg_cv x2;
        n3 = bounded_object_q_interval_neg_cv x3;
        n4 = bounded_object_q_interval_neg_cv x4;
        n5 = bounded_object_q_interval_neg_cv x5
    in
      [[n3;n3];
       [x3;x4;n5];
       [x3;n4;x5];
       [n0;n0;x1;x2;n3;n3;x4;x5];
       [x1;n2;x3];
       [n1;x2;x3];
       [n4;n4];
       [n3;x4;x5];
       [x0;n2;x4];
       [x0;n1;n1;x2;x3;n4;n4;x5];
       [n0;x2;x4];
       [n5;n5];
       [x0;n1;x5];
       [n0;x1;x5];
       [x0;x1;n2;n2;x3;x4;n5;n5];
       [n0;n0];
       [x0;x1;n5];
       [x0;x2;n4];
       [n1;n1];
       [x1;x2;n3];
       [n2;n2]]
End

Definition bounded_case16594_object_delta_hessian_rows_six_body_def:
  bounded_case16594_object_delta_hessian_rows_six_body =
    Let «n0» (App «candle_cv_q_interval_neg» [Var «x0»]) (Let «n1» (App «candle_cv_q_interval_neg» [Var «x1»]) (Let «n2» (App «candle_cv_q_interval_neg» [Var «x2»]) (Let «n3» (App «candle_cv_q_interval_neg» [Var «x3»]) (Let «n4» (App «candle_cv_q_interval_neg» [Var «x4»]) (Let «n5» (App «candle_cv_q_interval_neg» [Var «x5»]) (Let «row_lists» (Num 0) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_two» [Var «n2»;Var «n2»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x1»;Var «x2»;Var «n3»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_two» [Var «n1»;Var «n1»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x0»;Var «x2»;Var «n4»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x0»;Var «x1»;Var «n5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_two» [Var «n0»;Var «n0»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_eight» [Var «x0»;Var «x1»;Var «n2»;Var «n2»;Var «x3»;Var «x4»;Var «n5»;Var «n5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «n0»;Var «x1»;Var «x5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x0»;Var «n1»;Var «x5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_two» [Var «n5»;Var «n5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «n0»;Var «x2»;Var «x4»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_eight» [Var «x0»;Var «n1»;Var «n1»;Var «x2»;Var «x3»;Var «n4»;Var «n4»;Var «x5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x0»;Var «n2»;Var «x4»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «n3»;Var «x4»;Var «x5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_two» [Var «n4»;Var «n4»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «n1»;Var «x2»;Var «x3»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x1»;Var «n2»;Var «x3»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_eight» [Var «n0»;Var «n0»;Var «x1»;Var «x2»;Var «n3»;Var «n3»;Var «x4»;Var «x5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x3»;Var «n4»;Var «x5»]) (Var «row_lists»)) (Let «row_lists» (Pair (App «candle_cv_q_packed_delta_three» [Var «x3»;Var «x4»;Var «n5»]) (Var «row_lists»)) (Pair (App «candle_cv_q_packed_delta_two» [Var «n3»;Var «n3»]) (Var «row_lists»))))))))))))))))))))))))))))
End

Theorem bounded_case16594_object_delta_hessian_rows_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_hessian_rows_six» =
    SOME
      ([«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_hessian_rows_six_body)
Proof
  rw [bounded_case16594_object_delta_hessian_rows_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_hessian_rows_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_hessian_rows_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
         («x3»,from_cv x3);(«x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_hessian_rows_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp []
  >> ACCEPT_TAC bounded_case16594_object_delta_hessian_rows_six_lookup
QED

Theorem bounded_case16594_object_delta_hessian_rows_sums:
  bounded_object_q_interval_sums_cv
      (bounded_case16594_object_delta_hessian_rows_six_cv
        x0 x1 x2 x3 x4 x5) =
    bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5
Proof
  rw
    [bounded_case16594_object_delta_hessian_rows_six_cv_def,
     compute_boundedAnalyticObjectDeltaHessianRefinementTheory.bounded_object_q_delta_hessian_six_cv_def,
     compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_sums_cv_def]
QED

Theorem bounded_case16594_object_delta_hessian_rows_encoded:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] ==>
  EVERY (EVERY bounded_packed_q_interval_encoded)
    (bounded_case16594_object_delta_hessian_rows_six_cv
      x0 x1 x2 x3 x4 x5)
Proof
  strip_tac
  >> fs []
  >> rw [bounded_case16594_object_delta_hessian_rows_six_cv_def]
  >> simp
       [compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded]
QED

val _ = export_theory ();

