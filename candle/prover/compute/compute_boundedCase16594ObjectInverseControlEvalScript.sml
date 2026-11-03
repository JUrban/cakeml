(*****************************************************************************
 * Structural evaluator semantics for the object inverse operation.
 *
 * The three exact interval calculations and the shared unary-state update
 * remain explicit premises.  This theorem fixes their composition through
 * the authenticated production body without executing a genuine payload.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectInverseControlEval
Ancestors
  compute_boundedCase16594ObjectStateControlEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_state_inverse_body_def:
  bounded_case16594_object_state_inverse_body =
    App «candle_cv_q_packed_object_state_unary»
      [Var «radii»;Var «center_reciprocal»;
       App «candle_cv_q_packed_object_inverse_derivative»
         [Var «center_reciprocal»];
       App «candle_cv_q_packed_object_inverse_derivative»
         [Var «box_reciprocal»];
       App «candle_cv_q_packed_object_inverse_second»
         [Var «box_reciprocal»];
       Var «state»]
End

Theorem bounded_case16594_object_state_inverse_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_state_inverse» =
    SOME
      ([«radii»;«center_reciprocal»;«box_reciprocal»;«state»],
       bounded_case16594_object_state_inverse_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_compute_eval_literal_app4:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([name1;name2;name3;name4],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;
         from_cv argument3;from_cv argument4])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4)] body) refs
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

Theorem bounded_case16594_object_compute_eval_app6_argument_results:
  0 < clock /\
  compute_eval clock ceqs argument1 (refs:hol_refs) =
      (M_success (from_cv result1),refs) /\
  compute_eval clock ceqs argument2 refs =
      (M_success (from_cv result2),refs) /\
  compute_eval clock ceqs argument3 refs =
      (M_success (from_cv result3),refs) /\
  compute_eval clock ceqs argument4 refs =
      (M_success (from_cv result4),refs) /\
  compute_eval clock ceqs argument5 refs =
      (M_success (from_cv result5),refs) /\
  compute_eval clock ceqs argument6 refs =
      (M_success (from_cv result6),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;argument5;argument6]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;
         from_cv result4;from_cv result5;from_cv result6]) refs
Proof
  Cases_on `clock`
  >> simp []
  >> strip_tac
  >> Cases_on `ALOOKUP ceqs function_name`
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.option_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> Cases_on `x`
  >> Cases_on `LENGTH q = 6`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        holKernelTheory.raise_Failure_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_state_inverse_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_inverse»
        [from_cv radii;from_cv center_reciprocal;
         from_cv box_reciprocal;from_cv state_cv]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«radii»,from_cv radii);
         («center_reciprocal»,from_cv center_reciprocal);
         («box_reciprocal»,from_cv box_reciprocal);
         («state»,from_cv state_cv)]
        bounded_case16594_object_state_inverse_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app4
  >> asm_rewrite_tac []
  >> ACCEPT_TAC bounded_case16594_object_state_inverse_lookup
QED

Theorem bounded_case16594_object_state_inverse_eval_from_components:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_derivative»
        [from_cv center_reciprocal]) (refs:hol_refs) =
      (M_success (from_cv center_first),refs) /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_derivative»
        [from_cv box_reciprocal]) refs =
      (M_success (from_cv box_first),refs) /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_inverse_second»
        [from_cv box_reciprocal]) refs =
      (M_success (from_cv box_second),refs) /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_unary»
        [from_cv radii;from_cv center_reciprocal;from_cv center_first;
         from_cv box_first;from_cv box_second;from_cv state_cv]) refs =
      (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_inverse»
        [from_cv radii;from_cv center_reciprocal;
         from_cv box_reciprocal;from_cv state_cv]) refs =
      (M_success (from_cv result_state),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_state_inverse_unfold]
  >> simp
       [bounded_case16594_object_state_inverse_body_def,
        compute_evalTheory.subst_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_unary»
            [from_cv radii;from_cv center_reciprocal;from_cv center_first;
             from_cv box_first;from_cv box_second;from_cv state_cv]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app6_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
