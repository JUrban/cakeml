(*****************************************************************************
 * Structural evaluator semantics for production object-state addition.
 * Numerical center/list addition and recompletion remain explicit premises.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectAddControlEval
Ancestors
  compute_boundedCase16594ObjectAddEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_add_body_def:
  bounded_case16594_object_state_add_body =
    Let «center_value»
      (App «candle_cv_q_interval_add»
        [App «candle_cv_q_packed_object_state_center_value» [Var «left»];
         App «candle_cv_q_packed_object_state_center_value» [Var «right»]])
      (Let «center_gradient»
        (App «candle_cv_q_packed_object_interval_list_add»
          [App «candle_cv_q_packed_object_state_center_gradient»
             [Var «left»];
           App «candle_cv_q_packed_object_state_center_gradient»
             [Var «right»]])
        (Let «packed_hessian»
          (App «candle_cv_q_packed_object_interval_list_add»
            [App «candle_cv_q_packed_object_state_packed_hessian»
               [Var «left»];
             App «candle_cv_q_packed_object_state_packed_hessian»
               [Var «right»]])
          (App «candle_cv_q_packed_object_state_recomplete»
            [Var «radii»;
             App «candle_cv_bool_and»
               [App «candle_cv_q_packed_object_state_domain» [Var «left»];
                App «candle_cv_q_packed_object_state_domain» [Var «right»]];
             Var «center_value»;Var «center_gradient»;
             Var «packed_hessian»])))
End

Theorem bounded_case16594_object_state_add_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_add» =
    SOME
      ([«radii»;«left»;«right»],
       bounded_case16594_object_state_add_body)
Proof
  rw [bounded_case16594_object_state_add_body_def]
  >> EVAL_TAC
QED

Theorem bounded_case16594_object_state_add_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_add»
        [from_cv radii;from_cv left_cv;from_cv right_cv])
      (refs:hol_refs) =
    compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (subst [(«radii»,from_cv radii);(«left»,from_cv left_cv);
              («right»,from_cv right_cv)]
        bounded_case16594_object_state_add_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_literal_app3
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_add_lookup
QED

Theorem bounded_case16594_object_state_add_eval_from_components:
  4 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_add»
        [App «candle_cv_q_packed_object_state_center_value» [from_cv left_cv];
         App «candle_cv_q_packed_object_state_center_value» [from_cv right_cv]])
      (refs:hol_refs) = (M_success (from_cv next_center_value),refs) /\
  compute_eval (clock - 2) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [App «candle_cv_q_packed_object_state_center_gradient»
           [from_cv left_cv];
         App «candle_cv_q_packed_object_state_center_gradient»
           [from_cv right_cv]]) refs =
    (M_success (from_cv next_center_gradient),refs) /\
  compute_eval (clock - 3) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_interval_list_add»
        [App «candle_cv_q_packed_object_state_packed_hessian»
           [from_cv left_cv];
         App «candle_cv_q_packed_object_state_packed_hessian»
           [from_cv right_cv]]) refs =
    (M_success (from_cv next_packed_hessian),refs) /\
  compute_eval (clock - 4) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;
         App «candle_cv_bool_and»
           [App «candle_cv_q_packed_object_state_domain» [from_cv left_cv];
            App «candle_cv_q_packed_object_state_domain» [from_cv right_cv]];
         from_cv next_center_value;from_cv next_center_gradient;
         from_cv next_packed_hessian]) refs =
    (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_add»
        [from_cv radii;from_cv left_cv;from_cv right_cv]) refs =
    (M_success (from_cv result_state),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_add_unfold]
  >> simp
       [bounded_case16594_object_state_add_body_def,
        compute_evalTheory.subst_def]
  >> irule
       (Q.INST [`value` |-> `next_center_value`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_value`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_center_gradient`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_center_gradient`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (Q.INST [`value` |-> `next_packed_hessian`]
          compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_packed_hessian`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
