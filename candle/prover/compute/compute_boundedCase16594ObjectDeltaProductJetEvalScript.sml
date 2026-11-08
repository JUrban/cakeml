(*****************************************************************************
 * Exact arbitrary-input evaluator for the production 4*x_i*delta center jet.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaProductJetEval
Ancestors
  compute_boundedCase16594ObjectDeltaHessianSixEval
  compute_boundedCase16594ObjectDeltaProductSemanticBridge
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_value_six_packed_encoded:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] ==>
  bounded_packed_q_interval_encoded
    (bounded_object_q_delta_value_six_cv x0 x1 x2 x3 x4 x5)
Proof
  strip_tac
  >> fs []
  >> rw
       [compute_boundedAnalyticObjectDeltaValueRefinementTheory.bounded_object_q_delta_value_six_cv_def]
  >> irule
       compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded
  >> simp
       [compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded,
        compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_mul3_packed_encoded,
        compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded]
QED

Theorem bounded_case16594_object_delta_gradient_six_packed_encoded:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_case16594_object_delta_gradient_six_cv x0 x1 x2 x3 x4 x5)
Proof
  strip_tac
  >> fs []
  >> rw
       [compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_cv_def]
  >> simp
       [compute_boundedCase16594ObjectDeltaGradientCompleteEvalTheory.bounded_case16594_object_delta_pair_product_packed_encoded,
        compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded,
        compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded]
QED

Theorem bounded_case16594_object_delta_gradient_six_length:
  LENGTH
    (bounded_case16594_object_delta_gradient_six_cv x0 x1 x2 x3 x4 x5) = 6
Proof
  rw
    [compute_boundedCase16594ObjectDeltaGradientEvalTheory.bounded_case16594_object_delta_gradient_six_cv_def]
QED

Theorem bounded_case16594_object_delta_hessian_six_packed_encoded:
  EVERY bounded_packed_q_interval_encoded [x0;x1;x2;x3;x4;x5] ==>
  EVERY bounded_packed_q_interval_encoded
    (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5)
Proof
  strip_tac
  >> fs []
  >> rw
       [compute_boundedAnalyticObjectDeltaHessianRefinementTheory.bounded_object_q_delta_hessian_six_cv_def,
        compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_sums_cv_def]
  >> simp
       [compute_boundedCase16594ObjectDeltaValueEvalTheory.bounded_case16594_object_delta_neg_packed_encoded,
        compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_packed_encoded]
QED

Theorem bounded_case16594_object_delta_hessian_six_length:
  LENGTH (bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5) = 21
Proof
  rw
    [compute_boundedAnalyticObjectDeltaHessianRefinementTheory.bounded_object_q_delta_hessian_six_cv_def,
     compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_sums_cv_def]
QED

Theorem bounded_case16594_object_delta_product_hessian_length:
  !indices entries.
    LENGTH indices = LENGTH entries ==>
    LENGTH
      (bounded_case16594_object_delta_product_hessian_cv coordinate
        box_coordinate delta_gradient indices entries) = LENGTH indices
Proof
  Induct_on `indices`
  >- (gen_tac
      >> Cases_on `entries`
      >> simp
           [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `entries`
  >> simp
       [compute_boundedCase16594ObjectDeltaProductHessianCompleteEvalTheory.bounded_case16594_object_delta_product_hessian_cv_def]
QED

Definition bounded_case16594_object_delta_product_jet_six_cv_def:
  bounded_case16594_object_delta_product_jet_six_cv coordinate
      x0 x1 x2 x3 x4 x5 =
    let inputs = [x0;x1;x2;x3;x4;x5];
        coordinate_value = EL coordinate inputs;
        delta_value =
          bounded_object_q_delta_value_six_cv x0 x1 x2 x3 x4 x5;
        delta_gradient =
          bounded_case16594_object_delta_gradient_six_cv x0 x1 x2 x3 x4 x5;
        delta_hessian =
          bounded_object_q_delta_hessian_six_cv x0 x1 x2 x3 x4 x5;
        packed_hessian =
          bounded_case16594_object_delta_product_hessian_cv coordinate
            coordinate_value delta_gradient
            bounded_case16594_object_delta_product_indices6 delta_hessian
    in
      Pair
        (bounded_object_q_interval_scale4_cv
          (bounded_object_q_interval_mul_cv coordinate_value delta_value))
        (Pair
          (bounded_case16594_object_delta_product_center_gradient_six_cv
            coordinate coordinate_value delta_value delta_gradient)
          (bounded_object_q_cv_list
            (MAP bounded_object_q_cv_list
              (bounded_packed_q_source_hessian6_rows packed_hessian))))
End

Definition bounded_case16594_object_delta_product_jet_six_body_def:
  bounded_case16594_object_delta_product_jet_six_body =
    Let «inputs»
      (App «candle_cv_q_packed_delta_six»
        [Var «x0»;Var «x1»;Var «x2»;Var «x3»;Var «x4»;Var «x5»])
      (Let «coordinate_value»
        (App «candle_cv_q_interval_lookup»
          [Var «coordinate»;Var «inputs»])
        (Let «delta_value»
          (App «candle_cv_q_packed_delta_value_six»
            [Var «x0»;Var «x1»;Var «x2»;Var «x3»;Var «x4»;Var «x5»])
          (Let «delta_gradient»
            (App «candle_cv_q_packed_delta_gradient_six»
              [Var «x0»;Var «x1»;Var «x2»;Var «x3»;Var «x4»;Var «x5»])
            (Let «delta_hessian»
              (App «candle_cv_q_packed_delta_hessian_six»
                [Var «x0»;Var «x1»;Var «x2»;Var «x3»;Var «x4»;Var «x5»])
              (App «candle_cv_q_dim_jet_make»
                [App «candle_cv_q_packed_delta_product_center_value»
                  [Var «coordinate_value»;Var «delta_value»];
                 App «candle_cv_q_packed_delta_product_center_gradient_six»
                  [Var «coordinate»;Var «coordinate_value»;
                   Var «delta_value»;Var «delta_gradient»];
                 App «candle_cv_q_packed_hessian6_expand»
                  [App «candle_cv_q_packed_delta_product_hessian_six»
                    [Var «coordinate»;Var «coordinate_value»;
                     Var «delta_gradient»;Var «delta_hessian»]]])))))
End

Theorem bounded_case16594_object_delta_product_jet_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_jet_six» =
    SOME
      ([«coordinate»;«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_product_jet_six_body)
Proof
  rw [bounded_case16594_object_delta_product_jet_six_body_def]
  >> EVAL_TAC
QED

Definition bounded_case16594_object_delta_product_jet_environment_body_def:
  bounded_case16594_object_delta_product_jet_environment_body =
    App «candle_cv_q_packed_delta_product_jet_six»
      [Var «coordinate»;
       App «candle_cv_q_interval_lookup» [Num 0;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 1;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 2;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 3;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 4;Var «environment»];
       App «candle_cv_q_interval_lookup» [Num 5;Var «environment»]]
End

Theorem bounded_case16594_object_delta_product_jet_environment_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_product_jet_environment» =
    SOME
      ([«coordinate»;«environment»],
       bounded_case16594_object_delta_product_jet_environment_body)
Proof
  rw [bounded_case16594_object_delta_product_jet_environment_body_def]
  >> EVAL_TAC
QED

Definition bounded_case16594_object_q_dim_jet_make_body_def:
  bounded_case16594_object_q_dim_jet_make_body =
    Pair (Var «f») (Pair (Var «gradient») (Var «hessian»))
End

Theorem bounded_case16594_object_q_dim_jet_make_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_dim_jet_make» =
    SOME
      ([«f»;«gradient»;«hessian»],
       bounded_case16594_object_q_dim_jet_make_body)
Proof
  rw [bounded_case16594_object_q_dim_jet_make_body_def]
  >> EVAL_TAC
QED

val _ = export_theory ();
