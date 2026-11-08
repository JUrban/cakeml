(*****************************************************************************
 * Exact production-evaluator bridge for negating a canonical constant state.
 *
 * Rational, interval, gradient, and Hessian negation are discharged here.
 * The final theorem leaves only the two shared state-recompletion bounds as
 * explicit premises, isolating the next numerical bridge boundary.
 *****************************************************************************)
open compute_boundedCase16594ObjectPolyStepControlEvalTheory
open compute_boundedCase16594ObjectLinearEvalTheory

Theory compute_boundedCase16594ObjectStateNegEval
Ancestors
  compute_boundedCase16594ObjectLinearEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_compute_eval_app5_argument_results_for_neg:
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
      (M_success (from_cv result5),refs) ==>
  compute_eval clock ceqs
      (App function_name
        [argument1;argument2;argument3;argument4;argument5]) refs =
    compute_eval clock ceqs
      (App function_name
        [from_cv result1;from_cv result2;from_cv result3;
         from_cv result4;from_cv result5]) refs
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
  >> Cases_on `LENGTH q = 5`
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

Theorem bounded_case16594_object_constant_domain_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_domain»
        [from_cv (bounded_case16594_object_constant_state_cv payload)])
      (refs:hol_refs) = (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC [bounded_case16594_object_constant_state_cv_def]
  >> irule
       compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_domain_eval
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_constant_center_neg_eval:
  1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_interval_neg»
        [App «candle_cv_q_packed_object_state_center_value»
          [from_cv
            (bounded_case16594_object_constant_state_cv
              (Pair (Pair positive negative) denominator))]])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair
          (Pair (Pair negative positive) denominator)
          (Pair (Pair negative positive) denominator))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_interval_neg»
            [from_cv
              (Pair
                (Pair (Pair positive negative) denominator)
                (Pair (Pair positive negative) denominator))]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> PURE_REWRITE_TAC [bounded_case16594_object_constant_state_cv_def]
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_value_eval
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_q_interval_neg_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_constant_gradient_neg_eval:
  8 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_object_state_center_gradient»
          [from_cv (bounded_case16594_object_constant_state_cv payload)]])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_zero_gradient6_cv),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg»
            [from_cv bounded_case16594_object_zero_gradient6_cv]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> PURE_REWRITE_TAC [bounded_case16594_object_constant_state_cv_def]
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_center_gradient_eval
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_zero_gradient6_neg_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_constant_hessian_neg_eval:
  23 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_dim_interval_list_neg»
        [App «candle_cv_q_packed_object_state_packed_hessian»
          [from_cv (bounded_case16594_object_constant_state_cv payload)]])
      (refs:hol_refs) =
    (M_success
      (from_cv bounded_case16594_object_zero_hessian21_cv),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_dim_interval_list_neg»
            [from_cv bounded_case16594_object_zero_hessian21_cv]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> PURE_REWRITE_TAC [bounded_case16594_object_constant_state_cv_def]
      >> irule
           compute_boundedCase16594ObjectStateControlEvalTheory.bounded_case16594_object_state_packed_hessian_eval
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_zero_hessian21_neg_eval
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_constant_recomplete_after_neg_eval_from_bounds:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv radii;from_cv negated_center;
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv])
      (refs:hol_refs) = (M_success (from_cv value_bound),refs) /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv radii;
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) refs =
      (M_success (from_cv gradient_bounds),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_recomplete»
        [from_cv radii;
         App «candle_cv_q_packed_object_state_domain»
           [from_cv (bounded_case16594_object_constant_state_cv payload)];
         from_cv negated_center;
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) refs =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv
          (Num 1) negated_center
          bounded_case16594_object_zero_gradient6_cv
          value_bound gradient_bounds
          bounded_case16594_object_zero_hessian21_cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_state_recomplete»
            [from_cv radii;from_cv (Num 1);from_cv negated_center;
             from_cv bounded_case16594_object_zero_gradient6_cv;
             from_cv bounded_case16594_object_zero_hessian21_cv]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app5_argument_results_for_neg
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
      >> conj_tac
      >- (irule bounded_case16594_object_constant_domain_eval
          >> intLib.ARITH_TAC)
      >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
      >> conj_tac >- MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv
      >> MATCH_ACCEPT_TAC compute_execProofTheory.compute_eval_from_cv)
  >> irule
       compute_boundedCase16594ObjectRecompleteControlEvalTheory.bounded_case16594_object_state_recomplete_eval_from_bounds
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_state_neg_constant_eval_from_bounds:
  26 < clock /\
  compute_eval (clock - 5) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_value_bound6»
        [from_cv radii;
         from_cv
           (Pair (Pair (Pair negative positive) denominator)
             (Pair (Pair negative positive) denominator));
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv])
      (refs:hol_refs) = (M_success (from_cv value_bound),refs) /\
  compute_eval (clock - 5) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_gradient_complete6»
        [from_cv radii;
         from_cv bounded_case16594_object_zero_gradient6_cv;
         from_cv bounded_case16594_object_zero_hessian21_cv]) refs =
      (M_success (from_cv gradient_bounds),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_state_neg»
        [from_cv radii;
         from_cv
           (bounded_case16594_object_constant_state_cv
             (Pair (Pair positive negative) denominator))]) refs =
    (M_success
      (from_cv
        (bounded_case16594_object_state_cv
          (Num 1)
          (Pair (Pair (Pair negative positive) denominator)
            (Pair (Pair negative positive) denominator))
          bounded_case16594_object_zero_gradient6_cv
          value_bound gradient_bounds
          bounded_case16594_object_zero_hessian21_cv)),refs)
Proof
  strip_tac
  >> irule bounded_case16594_object_state_neg_eval_from_components
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_object_zero_gradient6_cv`
  >> qexists_tac
       `Pair (Pair (Pair negative positive) denominator)
          (Pair (Pair negative positive) denominator)`
  >> qexists_tac `bounded_case16594_object_zero_hessian21_cv`
  >> conj_tac
  >- (irule bounded_case16594_object_constant_center_neg_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_constant_hessian_neg_eval
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- (irule bounded_case16594_object_constant_gradient_neg_eval
      >> intLib.ARITH_TAC)
  >> irule
       bounded_case16594_object_constant_recomplete_after_neg_eval_from_bounds
  >> `(clock - 4) - 1 = clock - 5` by intLib.ARITH_TAC
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
