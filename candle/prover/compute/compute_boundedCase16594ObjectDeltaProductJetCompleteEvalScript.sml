(*****************************************************************************
 * Complete exact evaluator for the production 4*x_i*delta center jet.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductJetCompleteEval
Ancestors
  compute_boundedCase16594ObjectDeltaProductJetEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_q_dim_jet_make_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_jet_make»
        [from_cv center_value;from_cv gradient;from_cv hessian])
      (refs:hol_refs) =
    (M_success
      (Pair (from_cv center_value)
        (Pair (from_cv gradient) (from_cv hessian))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«f»,from_cv center_value);(«gradient»,from_cv gradient);
             («hessian»,from_cv hessian)]
            bounded_case16594_object_q_dim_jet_make_body) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
      >> simp
           [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_q_dim_jet_make_lookup])
  >> simp
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_q_dim_jet_make_body_def,
        compute_evalTheory.subst_def,compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_delta_product_hessian_six_length:
  LENGTH delta_hessian = 21 ==>
  LENGTH
    (bounded_case16594_object_delta_product_hessian_cv coordinate
      box_coordinate delta_gradient
      bounded_case16594_object_delta_product_indices6 delta_hessian) = 21
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `LENGTH bounded_case16594_object_delta_product_indices6`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_hessian_length
      >> simp
           [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def])
  >> simp
       [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_indices6_def]
QED

Theorem bounded_case16594_object_delta_product_jet_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_six»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«coordinate»,from_cv (Num coordinate));(«x0»,from_cv x0);
         («x1»,from_cv x1);(«x2»,from_cv x2);(«x3»,from_cv x3);
         («x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_product_jet_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> simp
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_jet_six_lookup]
QED

Theorem bounded_case16594_object_delta_product_jet_six_eval:
  coordinate < 6 /\
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  262144 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_product_jet_six»
        [from_cv (Num coordinate);from_cv x0;from_cv x1;from_cv x2;
         from_cv x3;from_cv x4;from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_delta_product_jet_six_cv coordinate
          x0 x1 x2 x3 x4 x5)),refs)
Proof
  strip_tac
  >> `bounded_packed_q_interval_encoded
        (EL coordinate [x0;x1;x2;x3;x4;x5])` by
       (`coordinate = 0 \/ coordinate = 1 \/ coordinate = 2 \/
         coordinate = 3 \/ coordinate = 4 \/ coordinate = 5` by
          intLib.ARITH_TAC
        >> fs [])
  >> `bounded_packed_q_interval_encoded
        (bounded_object_q_delta_value_six_cv x0 x1 x2 x3 x4 x5)` by
       (irule
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_value_six_packed_encoded
        >> simp [])
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5)` by
       (irule
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_packed_encoded
        >> simp [])
  >> `LENGTH
        (bounded_case16594_object_delta_gradient_six_cv
          x0 x1 x2 x3 x4 x5) = 6` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_gradient_six_length]
  >> `EVERY bounded_packed_q_interval_encoded
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5)` by
       (irule
          compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_packed_encoded
        >> simp [])
  >> `LENGTH
        (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) = 21` by
       simp
         [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_hessian_six_length]
  >> rw [bounded_case16594_object_delta_product_jet_six_unfold]
  >> simp
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_jet_six_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list [x0;x1;x2;x3;x4;x5]`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_delta_six_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `EL coordinate [x0;x1;x2;x3;x4;x5]`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_interval_lookup_el_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_delta_value_six_cv x0 x1 x2 x3 x4 x5`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_value_six_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_case16594_object_delta_gradient_six_cv
            x0 x1 x2 x3 x4 x5)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_gradient_six_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_cv_list
          (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaHessianSixEvalTheory.bounded_case16594_object_delta_hessian_six_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> rw
       [compute_boundedCase16594ObjectDeltaProductJetEvalTheory.bounded_case16594_object_delta_product_jet_six_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 6) bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_jet_make»
            [from_cv
              (bounded_object_q_interval_scale4_cv
                (bounded_object_q_interval_mul_cv
                  (EL coordinate [x0;x1;x2;x3;x4;x5])
                  (bounded_object_q_delta_value_six_cv
                    x0 x1 x2 x3 x4 x5)));
             from_cv
              (bounded_case16594_object_delta_product_center_gradient_six_cv
                coordinate (EL coordinate [x0;x1;x2;x3;x4;x5])
                (bounded_object_q_delta_value_six_cv x0 x1 x2 x3 x4 x5)
                (bounded_case16594_object_delta_gradient_six_cv
                  x0 x1 x2 x3 x4 x5));
             from_cv
              (bounded_object_q_cv_list
                (MAP bounded_object_q_cv_list
                  (bounded_packed_q_source_hessian6_rows
                    (bounded_case16594_object_delta_product_hessian_cv
                      coordinate (EL coordinate [x0;x1;x2;x3;x4;x5])
                      (bounded_case16594_object_delta_gradient_six_cv
                        x0 x1 x2 x3 x4 x5)
                      bounded_case16594_object_delta_product_indices6
                      (bounded_object_q_delta_hessian_six_cv
                        x0 x1 x2 x3 x4 x5)))))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_compute_eval_app3_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectDeltaLinearEvalTheory.bounded_case16594_object_delta_product_center_value_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              compute_boundedCase16594ObjectDeltaProductGradientSixEvalTheory.bounded_case16594_object_delta_product_center_gradient_six_eval)
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 6)
              bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_hessian6_expand»
                [from_cv
                  (bounded_object_q_cv_list
                    (bounded_case16594_object_delta_product_hessian_cv
                      coordinate (EL coordinate [x0;x1;x2;x3;x4;x5])
                      (bounded_case16594_object_delta_gradient_six_cv
                        x0 x1 x2 x3 x4 x5)
                      bounded_case16594_object_delta_product_indices6
                      (bounded_object_q_delta_hessian_six_cv
                        x0 x1 x2 x3 x4 x5)))]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectDeltaHessianSumsEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> irule
               (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                 compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_six_eval)
          >> simp []
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594ObjectGradientCompleteEvalTheory.bounded_case16594_object_hessian6_expand_eval
      >> simp [bounded_case16594_object_delta_product_hessian_six_length]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_q_dim_jet_make_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
