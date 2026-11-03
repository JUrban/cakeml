(*****************************************************************************
 * Canonical runtime representation and structural evaluator semantics for
 * one explicit-radius object Taylor state.
 *
 * Numerical fields remain opaque cv values.  This theory fixes only the
 * production six-field layout and proves the generated constructor and all
 * accessors against the authenticated case-16594 equation environment.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectStateControlEval
Ancestors
  compute_boundedCase16594ObjectCoreCongruence
  compute_boundedCase16594ObjectDispatchStepControlEval
Libs
  bossLib preamble

Definition bounded_case16594_object_state_cv_def:
  bounded_case16594_object_state_cv domain_cv center_value center_gradient
      value_bound gradient_bounds packed_hessian =
    Pair domain_cv
      (Pair center_value
        (Pair center_gradient
          (Pair value_bound (Pair gradient_bounds packed_hessian))))
End

Definition bounded_case16594_object_state_make_body_def:
  bounded_case16594_object_state_make_body =
    Pair (Var «domain»)
      (Pair (Var «center_value»)
        (Pair (Var «center_gradient»)
          (Pair (Var «value_bound»)
            (Pair (Var «gradient_bounds») (Var «packed_hessian»)))))
End

Theorem bounded_case16594_object_state_make_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_make» =
    SOME
      ([«domain»;«center_value»;«center_gradient»;«value_bound»;
        «gradient_bounds»;«packed_hessian»],
       bounded_case16594_object_state_make_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_compute_eval_literal_app1:
  0 < clock /\
  ALOOKUP ceqs function_name = SOME ([name],body) ==>
  compute_eval clock ceqs (App function_name [from_cv argument])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst [(name,from_cv argument)] body) refs
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

Theorem bounded_case16594_object_state_make_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_make»
        [from_cv domain_cv;from_cv center_value;from_cv center_gradient;
         from_cv value_bound;from_cv gradient_bounds;
         from_cv packed_hessian]) (refs:hol_refs) =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv domain_cv center_value
          center_gradient value_bound gradient_bounds packed_hessian)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«domain»,from_cv domain_cv);
             («center_value»,from_cv center_value);
             («center_gradient»,from_cv center_gradient);
             («value_bound»,from_cv value_bound);
             («gradient_bounds»,from_cv gradient_bounds);
             («packed_hessian»,from_cv packed_hessian)]
            bounded_case16594_object_state_make_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app6
      >> asm_rewrite_tac []
      >> ACCEPT_TAC bounded_case16594_object_state_make_lookup)
  >> simp
       [bounded_case16594_object_state_make_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Definition bounded_case16594_object_state_domain_body_def:
  bounded_case16594_object_state_domain_body = Uop Fst (Var «state»)
End

Definition bounded_case16594_object_state_center_value_body_def:
  bounded_case16594_object_state_center_value_body =
    Uop Fst (Uop Snd (Var «state»))
End

Definition bounded_case16594_object_state_center_gradient_body_def:
  bounded_case16594_object_state_center_gradient_body =
    Uop Fst (Uop Snd (Uop Snd (Var «state»)))
End

Definition bounded_case16594_object_state_value_bound_body_def:
  bounded_case16594_object_state_value_bound_body =
    Uop Fst (Uop Snd (Uop Snd (Uop Snd (Var «state»))))
End

Definition bounded_case16594_object_state_gradient_bounds_body_def:
  bounded_case16594_object_state_gradient_bounds_body =
    Uop Fst (Uop Snd (Uop Snd (Uop Snd (Uop Snd (Var «state»)))))
End

Definition bounded_case16594_object_state_packed_hessian_body_def:
  bounded_case16594_object_state_packed_hessian_body =
    Uop Snd (Uop Snd (Uop Snd (Uop Snd (Uop Snd (Var «state»)))))
End

Theorem bounded_case16594_object_state_accessor_lookups:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_domain» =
      SOME ([«state»],bounded_case16594_object_state_domain_body) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_center_value» =
      SOME ([«state»],bounded_case16594_object_state_center_value_body) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_center_gradient» =
      SOME ([«state»],bounded_case16594_object_state_center_gradient_body) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_value_bound» =
      SOME ([«state»],bounded_case16594_object_state_value_bound_body) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_gradient_bounds» =
      SOME ([«state»],bounded_case16594_object_state_gradient_bounds_body) /\
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_packed_hessian» =
      SOME ([«state»],bounded_case16594_object_state_packed_hessian_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_state_domain_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_domain» [from_cv
        (bounded_case16594_object_state_cv domain_cv center_value center_gradient
          value_bound gradient_bounds packed_hessian)]) (refs:hol_refs) =
      (M_success (from_cv domain_cv),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«state»,from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian))]
            bounded_case16594_object_state_domain_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app1
      >> asm_rewrite_tac []
      >> fs [bounded_case16594_object_state_accessor_lookups])
  >> simp
       [bounded_case16594_object_state_domain_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_center_value_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_center_value» [from_cv
        (bounded_case16594_object_state_cv domain_cv center_value center_gradient
          value_bound gradient_bounds packed_hessian)]) refs =
      (M_success (from_cv center_value),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«state»,from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian))]
            bounded_case16594_object_state_center_value_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app1
      >> asm_rewrite_tac []
      >> fs [bounded_case16594_object_state_accessor_lookups])
  >> simp
       [bounded_case16594_object_state_center_value_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_center_gradient_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_center_gradient» [from_cv
        (bounded_case16594_object_state_cv domain_cv center_value center_gradient
          value_bound gradient_bounds packed_hessian)]) refs =
      (M_success (from_cv center_gradient),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«state»,from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian))]
            bounded_case16594_object_state_center_gradient_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app1
      >> asm_rewrite_tac []
      >> fs [bounded_case16594_object_state_accessor_lookups])
  >> simp
       [bounded_case16594_object_state_center_gradient_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_value_bound_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_value_bound» [from_cv
        (bounded_case16594_object_state_cv domain_cv center_value center_gradient
          value_bound gradient_bounds packed_hessian)]) refs =
      (M_success (from_cv value_bound),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«state»,from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian))]
            bounded_case16594_object_state_value_bound_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app1
      >> asm_rewrite_tac []
      >> fs [bounded_case16594_object_state_accessor_lookups])
  >> simp
       [bounded_case16594_object_state_value_bound_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_gradient_bounds_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_gradient_bounds» [from_cv
        (bounded_case16594_object_state_cv domain_cv center_value center_gradient
          value_bound gradient_bounds packed_hessian)]) refs =
      (M_success (from_cv gradient_bounds),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«state»,from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian))]
            bounded_case16594_object_state_gradient_bounds_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app1
      >> asm_rewrite_tac []
      >> fs [bounded_case16594_object_state_accessor_lookups])
  >> simp
       [bounded_case16594_object_state_gradient_bounds_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_packed_hessian_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_packed_hessian» [from_cv
        (bounded_case16594_object_state_cv domain_cv center_value center_gradient
          value_bound gradient_bounds packed_hessian)]) refs =
      (M_success (from_cv packed_hessian),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst [(«state»,from_cv
            (bounded_case16594_object_state_cv domain_cv center_value
              center_gradient value_bound gradient_bounds packed_hessian))]
            bounded_case16594_object_state_packed_hessian_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_literal_app1
      >> asm_rewrite_tac []
      >> fs [bounded_case16594_object_state_accessor_lookups])
  >> simp
       [bounded_case16594_object_state_packed_hessian_body_def,
        bounded_case16594_object_state_cv_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.compute_eval_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
