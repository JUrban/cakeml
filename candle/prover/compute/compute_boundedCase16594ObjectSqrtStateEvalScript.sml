(*****************************************************************************
 * Complete production evaluator semantics for the object square-root state
 * wrapper.  Certificate checking is intentionally left to the sqrt-step
 * theory; this layer authenticates the negative second derivative and the
 * shared unary-state call once.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSqrtStateEval
Ancestors
  compute_boundedCase16594ObjectUnaryCompleteEval
  compute_boundedCase16594ObjectNegEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_sqrt_body_def:
  bounded_case16594_object_state_sqrt_body =
    App «candle_cv_q_packed_object_state_unary»
      [Var «radii»;Var «center_root»;Var «center_first»;
       Var «box_first»;
       App «candle_cv_q_interval_neg» [Var «box_second_reciprocal»];
       Var «state»]
End

Theorem bounded_case16594_object_state_sqrt_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_sqrt» =
    SOME
      ([«radii»;«center_root»;«center_first»;«box_first»;
        «box_second_reciprocal»;«state»],
       bounded_case16594_object_state_sqrt_body)
Proof
  rw [bounded_case16594_object_state_sqrt_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_state_sqrt_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_sqrt»
        [from_cv radii;from_cv center_root;from_cv center_first;
         from_cv box_first;from_cv box_second_reciprocal;
         from_cv state_cv]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«center_root»,from_cv center_root);
         («center_first»,from_cv center_first);
         («box_first»,from_cv box_first);
         («box_second_reciprocal»,from_cv box_second_reciprocal);
         («state»,from_cv state_cv)]
        bounded_case16594_object_state_sqrt_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_sqrt_lookup
QED

Theorem bounded_case16594_object_state_sqrt_eval:
  EVERY bounded_object_q_encoded radii /\
  LENGTH radii = 6 /\
  bounded_packed_q_interval_encoded center_root /\
  bounded_packed_q_interval_encoded center_first /\
  bounded_packed_q_interval_encoded box_first /\
  bounded_packed_q_interval_encoded box_second_reciprocal /\
  EVERY bounded_packed_q_interval_encoded center_gradient /\
  LENGTH center_gradient = 6 /\
  EVERY bounded_packed_q_interval_encoded gradient_bounds /\
  LENGTH gradient_bounds = 6 /\
  EVERY bounded_packed_q_interval_encoded packed_hessian /\
  LENGTH packed_hessian = 21 /\
  8194 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_sqrt»
        [from_cv (bounded_object_q_cv_list radii);from_cv center_root;
         from_cv center_first;from_cv box_first;
         from_cv box_second_reciprocal;
         from_cv
           (bounded_case16594_object_state_cv domain_cv center_value
             (bounded_object_q_cv_list center_gradient) value_bound
             (bounded_object_q_cv_list gradient_bounds)
             (bounded_object_q_cv_list packed_hessian))])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_unary_cv
          radii domain_cv center_root center_first box_first
          (bounded_object_q_interval_neg_cv box_second_reciprocal)
          center_gradient gradient_bounds packed_hessian)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_sqrt_unfold]
  >> simp
       [bounded_case16594_object_state_sqrt_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_unary»
            [from_cv (bounded_object_q_cv_list radii);from_cv center_root;
             from_cv center_first;from_cv box_first;
             from_cv
               (bounded_object_q_interval_neg_cv
                 box_second_reciprocal);
             from_cv
               (bounded_case16594_object_state_cv domain_cv center_value
                 (bounded_object_q_cv_list center_gradient) value_bound
                 (bounded_object_q_cv_list gradient_bounds)
                 (bounded_object_q_cv_list packed_hessian))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_compute_eval_app6_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           compute_boundedCase16594ObjectRuntimePreservationTheory.bounded_case16594_object_interval_neg_encoded_eval
      >> simp
           [compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded])
  >> irule
       compute_boundedCase16594ObjectUnaryCompleteEvalTheory.bounded_case16594_object_state_unary_eval
  >> simp
       [compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_encoded_packed,
        compute_boundedCase16594ObjectNegEvalTheory.bounded_object_q_interval_neg_cv_encoded,
        compute_boundedCase16594ObjectMulEvalTheory.bounded_case16594_packed_interval_object_encoded]
QED

val _ = export_theory ();
