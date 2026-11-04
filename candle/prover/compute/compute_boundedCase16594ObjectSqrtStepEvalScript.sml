(*****************************************************************************
 * Production evaluator semantics for the first genuine object square-root
 * step.  The numerical certificate contracts and state construction are
 * supplied by the preceding generic layers; this theory authenticates and
 * composes the actual list bindings and control flow.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtStepEval
Ancestors
  compute_boundedCase16594ObjectCertificateListEval
  compute_boundedCase16594ObjectSqrtStateEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_sqrt_step_body_def:
  bounded_case16594_object_sqrt_step_body =
    If (Uop Ispair (Var «stack»))
      (If
        (App «candle_cv_cval_list_has»
          [Num 5;Var «certificates»])
        (Let «item» (Uop Fst (Var «stack»))
          (Let «center_root»
            (App «candle_cv_cval_list_nth»
              [Num 0;Var «certificates»])
            (Let «box_root»
              (App «candle_cv_cval_list_nth»
                [Num 1;Var «certificates»])
              (Let «center_derivative»
                (App «candle_cv_cval_list_nth»
                  [Num 2;Var «certificates»])
                (Let «box_derivative»
                  (App «candle_cv_cval_list_nth»
                    [Num 3;Var «certificates»])
                  (Let «box_second_reciprocal»
                    (App «candle_cv_cval_list_nth»
                      [Num 4;Var «certificates»])
                    (Let «certificate_rest»
                      (App «candle_cv_cval_list_drop»
                        [Num 5;Var «certificates»])
                      (If
                        (App «candle_cv_bool_and»
                          [App «candle_cv_q_interval_sqrt_certificate»
                             [App
                                «candle_cv_q_packed_object_state_center_value»
                                [Var «item»];
                              Var «center_root»];
                           App «candle_cv_bool_and»
                             [App «candle_cv_q_interval_inv_certificate»
                                [App «candle_cv_q_interval_add»
                                   [Var «center_root»;Var «center_root»];
                                 Var «center_derivative»];
                              App «candle_cv_bool_and»
                                [App «candle_cv_q_interval_sqrt_certificate»
                                   [App
                                      «candle_cv_q_packed_object_state_value_bound»
                                      [Var «item»];
                                    Var «box_root»];
                                 App «candle_cv_bool_and»
                                   [App «candle_cv_q_interval_inv_certificate»
                                      [App «candle_cv_q_interval_add»
                                         [Var «box_root»;Var «box_root»];
                                       Var «box_derivative»];
                                    App
                                      «candle_cv_q_interval_inv_certificate»
                                      [App «candle_cv_q_interval_mul»
                                         [App «candle_cv_q_interval_add»
                                            [Var «box_root»;
                                             Var «box_root»];
                                          App «candle_cv_q_interval_add»
                                            [App
                                               «candle_cv_q_packed_object_state_value_bound»
                                               [Var «item»];
                                             App
                                               «candle_cv_q_packed_object_state_value_bound»
                                               [Var «item»]]];
                                       Var «box_second_reciprocal»]]]]])
                        (Pair (Num 1)
                          (Pair
                            (Pair
                              (App «candle_cv_q_packed_object_state_sqrt»
                                [Var «radii»;Var «center_root»;
                                 Var «center_derivative»;
                                 Var «box_derivative»;
                                 Var «box_second_reciprocal»;Var «item»])
                              (Uop Snd (Var «stack»)))
                            (Var «certificate_rest»)))
                        (Pair (Num 0)
                          (Pair (Var «stack») (Var «certificates»)))))))))))
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
      (Pair (Num 0) (Pair (Var «stack») (Var «certificates»)))
End

Definition bounded_case16594_object_sqrt_step_check_expression_def:
  bounded_case16594_object_sqrt_step_check_expression item center_root
      box_root center_derivative box_derivative box_second_reciprocal =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_sqrt_certificate»
         [App «candle_cv_q_packed_object_state_center_value» [from_cv item];
          from_cv center_root];
       App «candle_cv_bool_and»
         [App «candle_cv_q_interval_inv_certificate»
            [App «candle_cv_q_interval_add»
               [from_cv center_root;from_cv center_root];
             from_cv center_derivative];
          App «candle_cv_bool_and»
            [App «candle_cv_q_interval_sqrt_certificate»
               [App «candle_cv_q_packed_object_state_value_bound»
                  [from_cv item];
                from_cv box_root];
             App «candle_cv_bool_and»
               [App «candle_cv_q_interval_inv_certificate»
                  [App «candle_cv_q_interval_add»
                     [from_cv box_root;from_cv box_root];
                   from_cv box_derivative];
                App «candle_cv_q_interval_inv_certificate»
                  [App «candle_cv_q_interval_mul»
                     [App «candle_cv_q_interval_add»
                        [from_cv box_root;from_cv box_root];
                      App «candle_cv_q_interval_add»
                        [App «candle_cv_q_packed_object_state_value_bound»
                           [from_cv item];
                         App «candle_cv_q_packed_object_state_value_bound»
                           [from_cv item]]];
                   from_cv box_second_reciprocal]]]]]
End

Definition bounded_case16594_object_sqrt_step_success_expression_def:
  bounded_case16594_object_sqrt_step_success_expression radii item stack_rest
      center_root center_derivative box_derivative box_second_reciprocal
      certificate_rest =
    Pair (Num 1)
      (Pair
        (Pair
          (App «candle_cv_q_packed_object_state_sqrt»
            [from_cv radii;from_cv center_root;from_cv center_derivative;
             from_cv box_derivative;from_cv box_second_reciprocal;
             from_cv item])
          (from_cv stack_rest))
        (from_cv certificate_rest))
End

Theorem bounded_case16594_object_sqrt_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_sqrt_step» =
    SOME
      ([«radii»;«certificates»;«stack»],
       bounded_case16594_object_sqrt_step_body)
Proof
  rw [bounded_case16594_object_sqrt_step_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_sqrt_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_sqrt_step»
        [from_cv radii;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_case16594_object_sqrt_step_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> simp [bounded_case16594_object_sqrt_step_lookup]
QED

Theorem bounded_case16594_object_bool_and_true_argument_results:
  1 < clock /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      left_expression (refs:hol_refs) = (M_success (Num 1),refs) /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      right_expression refs = (M_success (Num 1),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_bool_and» [left_expression;right_expression]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_bool_and» [from_cv (Num 1);from_cv (Num 1)])
          refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [])
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         (Q.INST [`left_domain` |-> `T`, `right_domain` |-> `T`]
           compute_boundedCase16594ObjectMulCompleteEvalTheory.bounded_case16594_object_bool_and_flags_eval))
  >> simp []
QED

Theorem bounded_case16594_object_sqrt_certificate_argument_result:
  bounded_object_q_sqrt_certificate_exact input output /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      input_expression (refs:hol_refs) =
    (M_success (from_cv input),refs) /\
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_sqrt_certificate»
        [input_expression;from_cv output]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_sqrt_certificate»
            [from_cv input;from_cv output]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> irule
       compute_boundedCase16594ObjectSqrtCertificateExactEvalTheory.bounded_case16594_object_q_interval_sqrt_certificate_exact_eval
  >> simp []
QED

Theorem bounded_case16594_object_inv_certificate_argument_result:
  bounded_object_q_positive_inv_certificate_exact input output /\
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      input_expression (refs:hol_refs) =
    (M_success (from_cv input),refs) /\
  4 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [input_expression;from_cv output]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_inv_certificate»
            [from_cv input;from_cv output]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> irule
       compute_boundedCase16594ObjectInverseCertificateExactEvalTheory.bounded_case16594_object_q_interval_inv_certificate_exact_eval
  >> simp []
QED

Theorem bounded_case16594_object_sqrt_box_second_argument_eval:
  bounded_packed_q_interval_encoded box_root /\
  bounded_packed_q_interval_encoded value_bound /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv box_root box_root)
      (bounded_object_q_interval_add_cv value_bound value_bound))
    box_second_reciprocal /\
  12 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_inv_certificate»
        [App «candle_cv_q_interval_mul»
           [App «candle_cv_q_interval_add»
              [from_cv box_root;from_cv box_root];
            App «candle_cv_q_interval_add»
              [App «candle_cv_q_packed_object_state_value_bound»
                 [from_cv
                   (bounded_case16594_object_state_cv domain_cv center_value
                     center_gradient value_bound gradient_bounds hessian)];
               App «candle_cv_q_packed_object_state_value_bound»
                 [from_cv
                   (bounded_case16594_object_state_cv domain_cv center_value
                     center_gradient value_bound gradient_bounds hessian)]]];
         from_cv box_second_reciprocal]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_inv_certificate_argument_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `bounded_object_q_interval_mul_cv
          (bounded_object_q_interval_add_cv box_root box_root)
          (bounded_object_q_interval_add_cv value_bound value_bound)`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_mul_argument_results
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
            compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded,
            compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded,
            compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval]
      >> irule
           compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_argument_results
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_sqrt_step_check_eval:
  bounded_packed_q_interval_encoded center_root /\
  bounded_packed_q_interval_encoded box_root /\
  bounded_packed_q_interval_encoded value_bound /\
  bounded_object_q_sqrt_certificate_exact center_value center_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv center_root center_root)
    center_derivative /\
  bounded_object_q_sqrt_certificate_exact value_bound box_root /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_add_cv box_root box_root)
    box_derivative /\
  bounded_object_q_positive_inv_certificate_exact
    (bounded_object_q_interval_mul_cv
      (bounded_object_q_interval_add_cv box_root box_root)
      (bounded_object_q_interval_add_cv value_bound value_bound))
    box_second_reciprocal /\
  12 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_sqrt_step_check_expression
        (bounded_case16594_object_state_cv domain_cv center_value
          center_gradient value_bound gradient_bounds hessian)
        center_root box_root center_derivative box_derivative
        box_second_reciprocal) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_sqrt_step_check_expression_def]
  >> irule bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_sqrt_certificate_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `center_value`
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval])
  >> irule bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_inv_certificate_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `bounded_object_q_interval_add_cv center_root center_root`
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval])
  >> irule bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_sqrt_certificate_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `value_bound`
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval])
  >> irule bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule bounded_case16594_object_inv_certificate_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `bounded_object_q_interval_add_cv box_root box_root`
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval])
  >> irule bounded_case16594_object_sqrt_box_second_argument_eval
  >> simp []
QED

Theorem bounded_case16594_object_sqrt_step_success_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_root /\
  bounded_packed_q_interval_encoded center_derivative /\
  bounded_packed_q_interval_encoded box_derivative /\
  bounded_packed_q_interval_encoded box_second_reciprocal /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  8194 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_sqrt_step_success_expression
        (bounded_object_q_cv_list radii)
        (bounded_case16594_object_state_cv domain_cv center_value
          (bounded_object_q_cv_list center_gradient) value_bound
          (bounded_object_q_cv_list gradient_bounds)
          (bounded_object_q_cv_list packed_hessian))
        stack_rest center_root center_derivative box_derivative
        box_second_reciprocal certificate_rest) (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair
            (from_cv
              (bounded_case16594_object_state_unary_cv
                radii domain_cv center_root center_derivative box_derivative
                (bounded_object_q_interval_neg_cv box_second_reciprocal)
                center_gradient gradient_bounds packed_hessian))
            (from_cv stack_rest))
          (from_cv certificate_rest))),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_sqrt_step_success_expression_def]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
      >> conj_tac
      >- (irule
            compute_boundedCase16594ObjectSqrtStateEvalTheory.bounded_case16594_object_state_sqrt_eval
          >> simp [])
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
