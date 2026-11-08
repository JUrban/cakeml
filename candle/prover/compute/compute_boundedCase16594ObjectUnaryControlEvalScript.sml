(*****************************************************************************
 * Structural evaluator semantics for the shared object unary-state update.
 *
 * List scaling, unary Hessian construction, and state recompletion remain
 * explicit premises.  The two production lets, state accessors, and clock
 * threading are authenticated once for inverse, square root, and arctangent.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectUnaryControlEval
Ancestors
  compute_boundedCase16594ObjectRecompleteControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_unary_body_def:
  bounded_case16594_object_state_unary_body =
    Let «center_gradient»
      (App «candle_cv_q_packed_object_interval_list_scale»
        [Var «center_first»;
         App «candle_cv_q_packed_object_state_center_gradient»
           [Var «state»]])
      (Let «packed_hessian»
        (App «candle_cv_q_packed_object_unary_hessian6»
          [Var «box_first»;Var «box_second»;
           App «candle_cv_q_packed_object_state_gradient_bounds»
             [Var «state»];
           App «candle_cv_q_packed_object_state_packed_hessian»
             [Var «state»]])
        (App «candle_cv_q_packed_object_state_recomplete»
          [Var «radii»;
           App «candle_cv_q_packed_object_state_domain» [Var «state»];
           Var «result_interval»;Var «center_gradient»;
           Var «packed_hessian»]))
End

Theorem bounded_case16594_object_state_unary_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_unary» =
    SOME
      ([«radii»;«result_interval»;«center_first»;«box_first»;
        «box_second»;«state»],bounded_case16594_object_state_unary_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_state_unary_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_unary»
        [from_cv radii;from_cv result_interval;from_cv center_first;
         from_cv box_first;from_cv box_second;from_cv state_cv])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);
         («result_interval»,from_cv result_interval);
         («center_first»,from_cv center_first);
         («box_first»,from_cv box_first);
         («box_second»,from_cv box_second);
         («state»,from_cv state_cv)]
        bounded_case16594_object_state_unary_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app6
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_unary_lookup
QED

Theorem bounded_case16594_object_state_unary_eval_from_components:
  3 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_scale»
        [from_cv center_first;
         App «candle_cv_q_packed_object_state_center_gradient»
           [from_cv state_cv]]) (refs:hol_refs) =
      (M_success (from_cv next_center_gradient),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_unary_hessian6»
        [from_cv box_first;from_cv box_second;
         App «candle_cv_q_packed_object_state_gradient_bounds»
           [from_cv state_cv];
         App «candle_cv_q_packed_object_state_packed_hessian»
           [from_cv state_cv]]) refs =
      (M_success (from_cv next_packed_hessian),refs) /\
  compute_eval (clock - 3)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;
         App «candle_cv_q_packed_object_state_domain» [from_cv state_cv];
         from_cv result_interval;from_cv next_center_gradient;
         from_cv next_packed_hessian]) refs =
      (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_unary»
        [from_cv radii;from_cv result_interval;from_cv center_first;
         from_cv box_first;from_cv box_second;from_cv state_cv]) refs =
      (M_success (from_cv result_state),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_unary_unfold]
  >> simp
       [bounded_case16594_object_state_unary_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (Q.INST [`value` |-> `next_center_gradient`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_gradient`
  >> conj_tac >- asm_rewrite_tac []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_packed_hessian`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_packed_hessian`
  >> conj_tac >- asm_rewrite_tac []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
