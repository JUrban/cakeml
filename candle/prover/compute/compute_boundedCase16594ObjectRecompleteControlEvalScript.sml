(*****************************************************************************
 * Structural evaluator semantics for object-state recompletion.
 *
 * Value-bound and gradient-bound arithmetic remain explicit premises.  The
 * authenticated production body and canonical six-field result layout are
 * proved once here for every ordinary and specialized instruction family.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectRecompleteControlEval
Ancestors
  compute_boundedCase16594ObjectStateControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_recomplete_body_def:
  bounded_case16594_object_state_recomplete_body =
    App «candle_cv_q_packed_object_state_make»
      [Var «domain»;Var «center_value»;Var «center_gradient»;
       App «candle_cv_q_packed_object_value_bound6»
         [Var «radii»;Var «center_value»;Var «center_gradient»;
          Var «packed_hessian»];
       App «candle_cv_q_packed_object_gradient_complete6»
         [Var «radii»;Var «center_gradient»;Var «packed_hessian»];
       Var «packed_hessian»]
End

Theorem bounded_case16594_object_state_recomplete_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_recomplete» =
    SOME
      ([«radii»;«domain»;«center_value»;«center_gradient»;
        «packed_hessian»],bounded_case16594_object_state_recomplete_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_compute_eval_literal_app5:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([name1;name2;name3;name4;name5],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5)] body) refs
Proof
  Cases_on `clock`
  >> rw []
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> every_case_tac
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_object_state_recomplete_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;from_cv domain_cv;from_cv center_value;
         from_cv center_gradient;from_cv packed_hessian]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);(«domain»,from_cv domain_cv);
         («center_value»,from_cv center_value);
         («center_gradient»,from_cv center_gradient);
         («packed_hessian»,from_cv packed_hessian)]
        bounded_case16594_object_state_recomplete_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app5
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_recomplete_lookup
QED

Theorem bounded_case16594_object_state_recomplete_eval_from_bounds:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv radii;from_cv center_value;
         from_cv center_gradient;from_cv packed_hessian]) (refs:hol_refs) =
      (M_success (from_cv value_bound),refs) /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv radii;from_cv center_gradient;from_cv packed_hessian]) refs =
      (M_success (from_cv gradient_bounds),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;from_cv domain_cv;from_cv center_value;
         from_cv center_gradient;from_cv packed_hessian]) refs =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv domain_cv center_value
          center_gradient value_bound gradient_bounds packed_hessian)),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_recomplete_unfold]
  >> simp
       [bounded_case16594_object_state_recomplete_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_make»
            [from_cv domain_cv;from_cv center_value;from_cv center_gradient;
             from_cv value_bound;from_cv gradient_bounds;
             from_cv packed_hessian]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app6_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_state_make_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
