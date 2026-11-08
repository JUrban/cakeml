(*****************************************************************************
 * Exact evaluator semantics for the production compact delta gradient.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDeltaGradientEval
Ancestors
  compute_boundedCase16594ObjectDeltaValueEval
  compute_boundedCase16594ObjectDeltaPrimitiveEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_delta_sum11_argument_results:
  EVERY bounded_packed_q_interval_encoded
    [value0;value1;value2;value3;value4;value5;value6;value7;value8;
     value9;value10] /\
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
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression7 refs = (M_success (from_cv value7),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression8 refs = (M_success (from_cv value8),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression9 refs = (M_success (from_cv value9),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      expression10 refs = (M_success (from_cv value10),refs) /\
  256 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_sum»
        [App «candle_cv_q_packed_delta_eleven»
          [expression0;expression1;expression2;expression3;expression4;
           expression5;expression6;expression7;expression8;expression9;
           expression10]]) refs =
    (M_success
      (from_cv
        (bounded_object_q_interval_sum_cv
          [value0;value1;value2;value3;value4;value5;value6;value7;
           value8;value9;value10])),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_delta_sum»
            [from_cv
              (bounded_object_q_cv_list
                [value0;value1;value2;value3;value4;value5;value6;
                 value7;value8;value9;value10])]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
              (App «candle_cv_q_packed_delta_eleven»
                [from_cv value0;from_cv value1;from_cv value2;
                 from_cv value3;from_cv value4;from_cv value5;
                 from_cv value6;from_cv value7;from_cv value8;
                 from_cv value9;from_cv value10]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_compute_eval_app11_argument_results
          >> simp [])
      >> irule
           compute_boundedCase16594ObjectDeltaPrimitiveEvalTheory.bounded_case16594_object_delta_eleven_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectDeltaSumEvalTheory.bounded_case16594_object_delta_sum_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_object_delta_gradient_six_cv_def:
  bounded_case16594_object_delta_gradient_six_cv x0 x1 x2 x3 x4 x5 =
    let p00 = bounded_object_q_interval_mul_cv x0 x0;
        p01 = bounded_object_q_interval_mul_cv x0 x1;
        p02 = bounded_object_q_interval_mul_cv x0 x2;
        p03 = bounded_object_q_interval_mul_cv x0 x3;
        p04 = bounded_object_q_interval_mul_cv x0 x4;
        p05 = bounded_object_q_interval_mul_cv x0 x5;
        p11 = bounded_object_q_interval_mul_cv x1 x1;
        p12 = bounded_object_q_interval_mul_cv x1 x2;
        p13 = bounded_object_q_interval_mul_cv x1 x3;
        p14 = bounded_object_q_interval_mul_cv x1 x4;
        p15 = bounded_object_q_interval_mul_cv x1 x5;
        p22 = bounded_object_q_interval_mul_cv x2 x2;
        p23 = bounded_object_q_interval_mul_cv x2 x3;
        p24 = bounded_object_q_interval_mul_cv x2 x4;
        p25 = bounded_object_q_interval_mul_cv x2 x5;
        p33 = bounded_object_q_interval_mul_cv x3 x3;
        p34 = bounded_object_q_interval_mul_cv x3 x4;
        p35 = bounded_object_q_interval_mul_cv x3 x5;
        p44 = bounded_object_q_interval_mul_cv x4 x4;
        p45 = bounded_object_q_interval_mul_cv x4 x5;
        p55 = bounded_object_q_interval_mul_cv x5 x5;
        g0 = bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv p03;
           bounded_object_q_interval_neg_cv p03;p13;p14;
           bounded_object_q_interval_neg_cv p15;p23;
           bounded_object_q_interval_neg_cv p24;p25;
           bounded_object_q_interval_neg_cv p33;p34;p35];
        g1 = bounded_object_q_interval_sum_cv
          [p03;p04;bounded_object_q_interval_neg_cv p05;
           bounded_object_q_interval_neg_cv p14;
           bounded_object_q_interval_neg_cv p14;
           bounded_object_q_interval_neg_cv p23;p24;p25;p34;
           bounded_object_q_interval_neg_cv p44;p45];
        g2 = bounded_object_q_interval_sum_cv
          [p03;bounded_object_q_interval_neg_cv p04;p05;
           bounded_object_q_interval_neg_cv p13;p14;p15;
           bounded_object_q_interval_neg_cv p25;
           bounded_object_q_interval_neg_cv p25;p35;p45;
           bounded_object_q_interval_neg_cv p55];
        g3 = bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv p00;p01;p02;
           bounded_object_q_interval_neg_cv p03;
           bounded_object_q_interval_neg_cv p03;p04;p05;
           bounded_object_q_interval_neg_cv p12;p14;p25;
           bounded_object_q_interval_neg_cv p45];
        g4 = bounded_object_q_interval_sum_cv
          [p01;bounded_object_q_interval_neg_cv p02;p03;
           bounded_object_q_interval_neg_cv p11;p12;p13;
           bounded_object_q_interval_neg_cv p14;
           bounded_object_q_interval_neg_cv p14;p15;p25;
           bounded_object_q_interval_neg_cv p35];
        g5 = bounded_object_q_interval_sum_cv
          [bounded_object_q_interval_neg_cv p01;p02;p03;p12;p14;
           bounded_object_q_interval_neg_cv p22;p23;p24;
           bounded_object_q_interval_neg_cv p25;
           bounded_object_q_interval_neg_cv p25;
           bounded_object_q_interval_neg_cv p34]
    in
      [g0;g1;g2;g3;g4;g5]
End

Theorem bounded_case16594_object_delta_gradient_six_semantic:
  bounded_object_q_delta_gradient_from_products_cv
      (bounded_object_q_delta_pair_products_six_cv x0 x1 x2 x3 x4 x5) =
    SOME
      (bounded_case16594_object_delta_gradient_six_cv x0 x1 x2 x3 x4 x5)
Proof
  rw
    [bounded_case16594_object_delta_gradient_six_cv_def,
     compute_boundedAnalyticObjectDeltaProductRefinementTheory.bounded_object_q_delta_pair_products_six_cv_def,
     compute_boundedAnalyticObjectDeltaProductRefinementTheory.bounded_object_q_interval_list_pairwise_mul_cv_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_from_products_cv_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_components_cv_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_component_from_products_cv_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_gradient_signed_terms_cv_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_delta_gradient_signed_indices_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_select_signed_terms_cv_def,
     compute_boundedAnalyticObjectDeltaGradientRefinementTheory.bounded_object_q_delta_apply_signed_terms_cv_def,
     compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_sum_cv_def,
     compute_boundedAnalyticObjectDeltaLinearRefinementTheory.bounded_object_q_interval_sum_aux_cv_def,
     compute_boundedAnalyticObjectRefinementTheory.bounded_object_q_nth_def]
  >> EVAL_TAC
QED

Definition bounded_case16594_object_delta_gradient_six_body_def:
  bounded_case16594_object_delta_gradient_six_body =
    Let «p00» (App «candle_cv_q_interval_mul» [Var «x0»;Var «x0»]) (Let «p01» (App «candle_cv_q_interval_mul» [Var «x0»;Var «x1»]) (Let «p02» (App «candle_cv_q_interval_mul» [Var «x0»;Var «x2»]) (Let «p03» (App «candle_cv_q_interval_mul» [Var «x0»;Var «x3»]) (Let «p04» (App «candle_cv_q_interval_mul» [Var «x0»;Var «x4»]) (Let «p05» (App «candle_cv_q_interval_mul» [Var «x0»;Var «x5»]) (Let «p11» (App «candle_cv_q_interval_mul» [Var «x1»;Var «x1»]) (Let «p12» (App «candle_cv_q_interval_mul» [Var «x1»;Var «x2»]) (Let «p13» (App «candle_cv_q_interval_mul» [Var «x1»;Var «x3»]) (Let «p14» (App «candle_cv_q_interval_mul» [Var «x1»;Var «x4»]) (Let «p15» (App «candle_cv_q_interval_mul» [Var «x1»;Var «x5»]) (Let «p22» (App «candle_cv_q_interval_mul» [Var «x2»;Var «x2»]) (Let «p23» (App «candle_cv_q_interval_mul» [Var «x2»;Var «x3»]) (Let «p24» (App «candle_cv_q_interval_mul» [Var «x2»;Var «x4»]) (Let «p25» (App «candle_cv_q_interval_mul» [Var «x2»;Var «x5»]) (Let «p33» (App «candle_cv_q_interval_mul» [Var «x3»;Var «x3»]) (Let «p34» (App «candle_cv_q_interval_mul» [Var «x3»;Var «x4»]) (Let «p35» (App «candle_cv_q_interval_mul» [Var «x3»;Var «x5»]) (Let «p44» (App «candle_cv_q_interval_mul» [Var «x4»;Var «x4»]) (Let «p45» (App «candle_cv_q_interval_mul» [Var «x4»;Var «x5»]) (Let «p55» (App «candle_cv_q_interval_mul» [Var «x5»;Var «x5»]) (Let «g0» (App «candle_cv_q_packed_delta_sum» [App «candle_cv_q_packed_delta_eleven» [App «candle_cv_q_interval_neg» [Var «p03»];App «candle_cv_q_interval_neg» [Var «p03»];Var «p13»;Var «p14»;App «candle_cv_q_interval_neg» [Var «p15»];Var «p23»;App «candle_cv_q_interval_neg» [Var «p24»];Var «p25»;App «candle_cv_q_interval_neg» [Var «p33»];Var «p34»;Var «p35»]]) (Let «g1» (App «candle_cv_q_packed_delta_sum» [App «candle_cv_q_packed_delta_eleven» [Var «p03»;Var «p04»;App «candle_cv_q_interval_neg» [Var «p05»];App «candle_cv_q_interval_neg» [Var «p14»];App «candle_cv_q_interval_neg» [Var «p14»];App «candle_cv_q_interval_neg» [Var «p23»];Var «p24»;Var «p25»;Var «p34»;App «candle_cv_q_interval_neg» [Var «p44»];Var «p45»]]) (Let «g2» (App «candle_cv_q_packed_delta_sum» [App «candle_cv_q_packed_delta_eleven» [Var «p03»;App «candle_cv_q_interval_neg» [Var «p04»];Var «p05»;App «candle_cv_q_interval_neg» [Var «p13»];Var «p14»;Var «p15»;App «candle_cv_q_interval_neg» [Var «p25»];App «candle_cv_q_interval_neg» [Var «p25»];Var «p35»;Var «p45»;App «candle_cv_q_interval_neg» [Var «p55»]]]) (Let «g3» (App «candle_cv_q_packed_delta_sum» [App «candle_cv_q_packed_delta_eleven» [App «candle_cv_q_interval_neg» [Var «p00»];Var «p01»;Var «p02»;App «candle_cv_q_interval_neg» [Var «p03»];App «candle_cv_q_interval_neg» [Var «p03»];Var «p04»;Var «p05»;App «candle_cv_q_interval_neg» [Var «p12»];Var «p14»;Var «p25»;App «candle_cv_q_interval_neg» [Var «p45»]]]) (Let «g4» (App «candle_cv_q_packed_delta_sum» [App «candle_cv_q_packed_delta_eleven» [Var «p01»;App «candle_cv_q_interval_neg» [Var «p02»];Var «p03»;App «candle_cv_q_interval_neg» [Var «p11»];Var «p12»;Var «p13»;App «candle_cv_q_interval_neg» [Var «p14»];App «candle_cv_q_interval_neg» [Var «p14»];Var «p15»;Var «p25»;App «candle_cv_q_interval_neg» [Var «p35»]]]) (Let «g5» (App «candle_cv_q_packed_delta_sum» [App «candle_cv_q_packed_delta_eleven» [App «candle_cv_q_interval_neg» [Var «p01»];Var «p02»;Var «p03»;Var «p12»;Var «p14»;App «candle_cv_q_interval_neg» [Var «p22»];Var «p23»;Var «p24»;App «candle_cv_q_interval_neg» [Var «p25»];App «candle_cv_q_interval_neg» [Var «p25»];App «candle_cv_q_interval_neg» [Var «p34»]]]) (App «candle_cv_q_packed_delta_six» [Var «g0»;Var «g1»;Var «g2»;Var «g3»;Var «g4»;Var «g5»])))))))))))))))))))))))))))
End

Theorem bounded_case16594_object_delta_gradient_six_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_delta_gradient_six» =
    SOME
      ([«x0»;«x1»;«x2»;«x3»;«x4»;«x5»],
       bounded_case16594_object_delta_gradient_six_body)
Proof
  rw [bounded_case16594_object_delta_gradient_six_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_delta_gradient_six_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_delta_gradient_six»
        [from_cv x0;from_cv x1;from_cv x2;from_cv x3;from_cv x4;
         from_cv x5]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«x0»,from_cv x0);(«x1»,from_cv x1);(«x2»,from_cv x2);
         («x3»,from_cv x3);(«x4»,from_cv x4);(«x5»,from_cv x5)]
        bounded_case16594_object_delta_gradient_six_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp []
  >> ACCEPT_TAC bounded_case16594_object_delta_gradient_six_lookup
QED

val _ = export_theory ();
