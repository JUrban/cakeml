(*****************************************************************************
 * Production evaluator semantics for a successful object inverse step.
 * This layer authenticates the exact two-certificate guard and the successful
 * state/stack result independently of the surrounding list-binding control.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseStepEval
Ancestors
  compute_boundedCase16594ObjectSqrtStepEval
  compute_boundedCase16594ObjectInverseStateEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_inverse_step_body_def:
  bounded_case16594_object_inverse_step_body =
    If (Uop Ispair (Var «stack»))
      (If
        (App «candle_cv_cval_list_has» [Num 2;Var «certificates»])
        (Let «item» (Uop Fst (Var «stack»))
          (Let «center_reciprocal»
            (App «candle_cv_cval_list_nth»
              [Num 0;Var «certificates»])
            (Let «box_reciprocal»
              (App «candle_cv_cval_list_nth»
                [Num 1;Var «certificates»])
              (Let «certificate_rest»
                (App «candle_cv_cval_list_drop»
                  [Num 2;Var «certificates»])
                (If
                  (App «candle_cv_bool_and»
                    [App «candle_cv_q_interval_inv_certificate»
                       [App «candle_cv_q_packed_object_state_center_value»
                          [Var «item»];
                        Var «center_reciprocal»];
                     App «candle_cv_q_interval_inv_certificate»
                       [App «candle_cv_q_packed_object_state_value_bound»
                          [Var «item»];
                        Var «box_reciprocal»]])
                  (Pair (Num 1)
                    (Pair
                      (Pair
                        (App «candle_cv_q_packed_object_state_inverse»
                          [Var «radii»;Var «center_reciprocal»;
                           Var «box_reciprocal»;Var «item»])
                        (Uop Snd (Var «stack»)))
                      (Var «certificate_rest»)))
                  (Pair (Num 0)
                    (Pair (Var «stack») (Var «certificates»))))))))
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
      (Pair (Num 0) (Pair (Var «stack») (Var «certificates»)))
End

Definition bounded_case16594_object_inverse_step_check_expression_def:
  bounded_case16594_object_inverse_step_check_expression item
      center_reciprocal box_reciprocal =
    App «candle_cv_bool_and»
      [App «candle_cv_q_interval_inv_certificate»
         [App «candle_cv_q_packed_object_state_center_value» [from_cv item];
          from_cv center_reciprocal];
       App «candle_cv_q_interval_inv_certificate»
         [App «candle_cv_q_packed_object_state_value_bound» [from_cv item];
          from_cv box_reciprocal]]
End

Definition bounded_case16594_object_inverse_step_success_expression_def:
  bounded_case16594_object_inverse_step_success_expression radii item
      stack_rest center_reciprocal box_reciprocal certificate_rest =
    Pair (Num 1)
      (Pair
        (Pair
          (App «candle_cv_q_packed_object_state_inverse»
            [from_cv radii;from_cv center_reciprocal;
             from_cv box_reciprocal;from_cv item])
          (from_cv stack_rest))
        (from_cv certificate_rest))
End

Theorem bounded_case16594_object_inverse_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_inv_step» =
    SOME
      ([«radii»;«certificates»;«stack»],
       bounded_case16594_object_inverse_step_body)
Proof
  rw [bounded_case16594_object_inverse_step_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_inverse_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inv_step»
        [from_cv radii;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_case16594_object_inverse_step_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> simp [bounded_case16594_object_inverse_step_lookup]
QED

Theorem bounded_case16594_object_inverse_step_check_eval:
  bounded_object_q_positive_inv_certificate_exact
      center_value center_reciprocal /\
  bounded_object_q_positive_inv_certificate_exact
      value_bound box_reciprocal /\
  5 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_inverse_step_check_expression
        (bounded_case16594_object_state_cv domain_cv center_value
          center_gradient value_bound gradient_bounds hessian)
        center_reciprocal box_reciprocal) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_inverse_step_check_expression_def]
  >> irule
       compute_boundedCase16594ObjectSqrtStepEvalTheory.bounded_case16594_object_bool_and_true_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectSqrtStepEvalTheory.bounded_case16594_object_inv_certificate_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `center_value`
      >> simp
           [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval])
  >> irule
       compute_boundedCase16594ObjectSqrtStepEvalTheory.bounded_case16594_object_inv_certificate_argument_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `value_bound`
  >> simp
       [compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval]
QED

Theorem bounded_case16594_object_inverse_step_success_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_reciprocal /\
  bounded_packed_q_interval_encoded box_reciprocal /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  8194 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (bounded_case16594_object_inverse_step_success_expression
        (bounded_object_q_cv_list radii)
        (bounded_case16594_object_state_cv domain_cv center_value
          (bounded_object_q_cv_list center_gradient) value_bound
          (bounded_object_q_cv_list gradient_bounds)
          (bounded_object_q_cv_list packed_hessian))
        stack_rest center_reciprocal box_reciprocal certificate_rest)
      (refs:hol_refs) =
    (M_success
      (Pair (Num 1)
        (Pair
          (Pair
            (from_cv
              (bounded_case16594_object_state_unary_cv radii domain_cv
                center_reciprocal
                (bounded_object_q_interval_neg_cv
                  (bounded_object_q_interval_mul_cv
                    center_reciprocal center_reciprocal))
                (bounded_object_q_interval_neg_cv
                  (bounded_object_q_interval_mul_cv
                    box_reciprocal box_reciprocal))
                (bounded_object_q_interval_add_cv
                  (bounded_object_q_interval_mul_cv
                    (bounded_object_q_interval_mul_cv
                      box_reciprocal box_reciprocal) box_reciprocal)
                  (bounded_object_q_interval_mul_cv
                    (bounded_object_q_interval_mul_cv
                      box_reciprocal box_reciprocal) box_reciprocal))
                center_gradient gradient_bounds packed_hessian))
            (from_cv stack_rest))
          (from_cv certificate_rest))),refs)
Proof
  strip_tac
  >> rewrite_tac
       [bounded_case16594_object_inverse_step_success_expression_def]
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
            compute_boundedCase16594ObjectInverseStateEvalTheory.bounded_case16594_object_state_inverse_eval
          >> simp [])
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

val _ = export_theory ();
