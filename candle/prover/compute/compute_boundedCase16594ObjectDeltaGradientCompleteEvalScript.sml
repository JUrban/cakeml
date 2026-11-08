(*****************************************************************************
 * Complete exact evaluator theorem for the production compact delta gradient.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaGradientCompleteEval
Ancestors
  compute_boundedCase16594ObjectDeltaGradientEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_pair_product_packed_encoded:
  bounded_packed_q_interval_encoded left /\
  bounded_packed_q_interval_encoded right ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_interval_mul_cv left right)
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

fun bounded_case16594_object_delta_pair_product_let_tac result =
  irule
    compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac result
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectInverseCoreCongruenceTheory.bounded_case16594_object_q_interval_mul_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv];

fun bounded_case16594_object_delta_gradient_sum_let_tac result =
  irule
    compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac result
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_sum11_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            bounded_case16594_object_delta_pair_product_packed_encoded,
            compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded]
      >> rpt conj_tac
      >> TRY
           (irule
              compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_packed_interval_neg_eval
            >> simp
                 [bounded_case16594_object_delta_pair_product_packed_encoded]
            >> intLib.ARITH_TAC)
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv];

Theorem bounded_case16594_object_delta_gradient_six_eval:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] /\
  65536 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_gradient_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_cv_list
          (bounded_case16594_object_delta_gradient_six_cv
            x0 x1 x2 x3 x4 x5))),refs)
Proof
  strip_tac
  >> fs []
  >> rw
       [compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_unfold]
  >> simp
       [compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_body_def,
        compute_evalTheory.subst_def]
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x0 x0`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x0 x1`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x0 x2`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x0 x3`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x0 x4`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x0 x5`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x1 x1`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x1 x2`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x1 x3`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x1 x4`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x1 x5`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x2 x2`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x2 x3`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x2 x4`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x2 x5`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x3 x3`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x3 x4`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x3 x5`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x4 x4`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x4 x5`
  >> bounded_case16594_object_delta_pair_product_let_tac
       `bounded_object_q_interval_mul_cv x5 x5`
  >> bounded_case16594_object_delta_gradient_sum_let_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x3);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x3);
           bounded_object_q_interval_mul_cv x1 x3;
           bounded_object_q_interval_mul_cv x1 x4;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x5);
           bounded_object_q_interval_mul_cv x2 x3;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x4);
           bounded_object_q_interval_mul_cv x2 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x3 x3);
           bounded_object_q_interval_mul_cv x3 x4;
           bounded_object_q_interval_mul_cv x3 x5]`
  >> bounded_case16594_object_delta_gradient_sum_let_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_mul_cv x0 x3;
           bounded_object_q_interval_mul_cv x0 x4;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x5);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x4);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x4);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x3);
           bounded_object_q_interval_mul_cv x2 x4;
           bounded_object_q_interval_mul_cv x2 x5;
           bounded_object_q_interval_mul_cv x3 x4;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x4 x4);
           bounded_object_q_interval_mul_cv x4 x5]`
  >> bounded_case16594_object_delta_gradient_sum_let_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_mul_cv x0 x3;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x4);
           bounded_object_q_interval_mul_cv x0 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x3);
           bounded_object_q_interval_mul_cv x1 x4;
           bounded_object_q_interval_mul_cv x1 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x5);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x5);
           bounded_object_q_interval_mul_cv x3 x5;
           bounded_object_q_interval_mul_cv x4 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x5 x5)]`
  >> bounded_case16594_object_delta_gradient_sum_let_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x0);
           bounded_object_q_interval_mul_cv x0 x1;
           bounded_object_q_interval_mul_cv x0 x2;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x3);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x3);
           bounded_object_q_interval_mul_cv x0 x4;
           bounded_object_q_interval_mul_cv x0 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x2);
           bounded_object_q_interval_mul_cv x1 x4;
           bounded_object_q_interval_mul_cv x2 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x4 x5)]`
  >> bounded_case16594_object_delta_gradient_sum_let_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_mul_cv x0 x1;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x2);
           bounded_object_q_interval_mul_cv x0 x3;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x1);
           bounded_object_q_interval_mul_cv x1 x2;
           bounded_object_q_interval_mul_cv x1 x3;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x4);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x1 x4);
           bounded_object_q_interval_mul_cv x1 x5;
           bounded_object_q_interval_mul_cv x2 x5;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x3 x5)]`
  >> bounded_case16594_object_delta_gradient_sum_let_tac
       `bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x0 x1);
           bounded_object_q_interval_mul_cv x0 x2;
           bounded_object_q_interval_mul_cv x0 x3;
           bounded_object_q_interval_mul_cv x1 x2;
           bounded_object_q_interval_mul_cv x1 x4;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x2);
           bounded_object_q_interval_mul_cv x2 x3;
           bounded_object_q_interval_mul_cv x2 x4;
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x5);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x2 x5);
           bounded_object_q_interval_neg_cv
             (bounded_object_q_interval_mul_cv x3 x4)]`
  >> rw
       [compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_six_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
