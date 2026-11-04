(*****************************************************************************
 * Production evaluator semantics for the object atan state constructor.
 * Only the atan second-derivative scalar is new; the gradient, Hessian, and
 * recompletion work is delegated to the shared unary-state theorem.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAtanStateEval
Ancestors
  compute_boundedCase16594ObjectAtanStepCheckEval
  compute_boundedCase16594ObjectUnaryCompleteEval
  compute_boundedCase16594ObjectMulEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_atan_second_body_def:
  bounded_case16594_object_atan_second_body =
    App «candle_cv_q_interval_neg»
      [App «candle_cv_q_interval_mul»
        [App «candle_cv_q_interval_add»
          [Var «source»;Var «source»];
         Var «derivative_square»]]
End

Definition bounded_case16594_object_state_atan_body_def:
  bounded_case16594_object_state_atan_body =
    App «candle_cv_q_packed_object_state_unary»
      [Var «radii»;Var «center_result»;Var «center_first»;
       Var «box_first»;
       App «candle_cv_q_packed_object_atn_second»
         [App «candle_cv_q_packed_object_state_value_bound»
           [Var «state»];
          Var «box_first_square»];
       Var «state»]
End

Theorem bounded_case16594_object_atan_second_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_atn_second» =
    SOME
      ([«source»;«derivative_square»],
       bounded_case16594_object_atan_second_body)
Proof
  rw [bounded_case16594_object_atan_second_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_atan_second_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_atn_second»
        [from_cv source;from_cv derivative_square]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«source»,from_cv source);
         («derivative_square»,from_cv derivative_square)]
        bounded_case16594_object_atan_second_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app2
  >> simp [bounded_case16594_object_atan_second_lookup]
QED

Theorem bounded_case16594_object_atan_second_encoded:
  bounded_packed_q_interval_encoded source /\
  bounded_packed_q_interval_encoded derivative_square ==>
  bounded_object_q_interval_encoded
    (bounded_object_q_atan_second_cv source derivative_square)
Proof
  strip_tac
  >> rw
       [compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_second_cv_def]
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_neg_cv_encoded
  >> irule
       compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded
  >> simp
       [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded]
QED

Theorem bounded_case16594_object_atan_second_eval:
  bounded_packed_q_interval_encoded source /\
  bounded_packed_q_interval_encoded derivative_square /\
  12 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_atn_second»
        [from_cv source;from_cv derivative_square]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_atan_second_cv source derivative_square)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_atan_second_unfold]
  >> simp
       [bounded_case16594_object_atan_second_body_def,
        compute_evalTheory.subst_def,
        compute_boundedAnalyticObjectAtanOperationRefinementTheory.bounded_object_q_atan_second_cv_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_neg»
            [from_cv
              (bounded_object_q_interval_mul_cv
                (bounded_object_q_interval_add_cv source source)
                derivative_square)]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectLinearEvalTheory.bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule
           compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_mul_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_add_eval,
            compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded,
            compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded,
            compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded]
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_neg_encoded_eval
  >> simp
       [compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_mul_cv_encoded,
        compute_boundedObjectTaylorZeroAlgebraTheory.bounded_object_q_interval_add_cv_encoded,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_atan_second_state_value_eval:
  bounded_packed_q_interval_encoded value_bound /\
  bounded_packed_q_interval_encoded derivative_square /\
  13 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_atn_second»
        [App «candle_cv_q_packed_object_state_value_bound»
          [from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds hessian)];
         from_cv derivative_square]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_object_q_atan_second_cv
          value_bound derivative_square)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_atn_second»
            [from_cv value_bound;from_cv derivative_square]) refs`
  >> conj_tac
  >- (irule
        compute_boundedPackedObjectPrimitiveAbsEvalTheory.bounded_packed_compute_eval_app2_argument_results
      >> simp
           [compute_execProofTheory.compute_eval_from_cv,
            compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_value_bound_eval]
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_atan_second_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_state_atan_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_atn» =
    SOME
      ([«radii»;«center_result»;«center_first»;«box_first»;
        «box_first_square»;«state»],
       bounded_case16594_object_state_atan_body)
Proof
  rw [bounded_case16594_object_state_atan_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_state_atan_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_atn»
        [from_cv radii;from_cv center_result;from_cv center_first;
         from_cv box_first;from_cv box_first_square;from_cv state_cv])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_result»,from_cv center_result);
         («center_first»,from_cv center_first);
         («box_first»,from_cv box_first);
         («box_first_square»,from_cv box_first_square);
         («state»,from_cv state_cv)]
        bounded_case16594_object_state_atan_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> simp [bounded_case16594_object_state_atan_lookup]
QED

Theorem bounded_case16594_object_state_atan_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_result /\
  bounded_packed_q_interval_encoded center_first /\
  bounded_packed_q_interval_encoded box_first /\
  bounded_packed_q_interval_encoded box_first_square /\
  bounded_packed_q_interval_encoded value_bound /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  8194 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_atn»
        [from_cv (bounded_object_q_cv_list radii);from_cv center_result;
         from_cv center_first;from_cv box_first;from_cv box_first_square;
         from_cv
           (bounded_case16594_object_state_cv domain_cv center_value
             (bounded_object_q_cv_list center_gradient) value_bound
             (bounded_object_q_cv_list gradient_bounds)
             (bounded_object_q_cv_list packed_hessian))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_unary_cv
          radii domain_cv center_result center_first box_first
          (bounded_object_q_atan_second_cv
            value_bound box_first_square)
          center_gradient gradient_bounds packed_hessian)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_atan_unfold]
  >> simp
       [bounded_case16594_object_state_atan_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_unary»
            [from_cv (bounded_object_q_cv_list radii);from_cv center_result;
             from_cv center_first;from_cv box_first;
             from_cv
               (bounded_object_q_atan_second_cv
                 value_bound box_first_square);
             from_cv
               (bounded_case16594_object_state_cv domain_cv center_value
                 (bounded_object_q_cv_list center_gradient) value_bound
                 (bounded_object_q_cv_list gradient_bounds)
                 (bounded_object_q_cv_list packed_hessian))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule bounded_case16594_object_atan_second_state_value_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectUnaryCompleteEvalTheory.bounded_case16594_object_state_unary_eval
  >> simp
       [compute_boundedCase16594ObjectAtanAlgebraicCertificateEvalTheory.bounded_case16594_object_atan_derivative_square_eval,
        bounded_case16594_object_atan_second_encoded,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_object_interval_packed_encoded]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
