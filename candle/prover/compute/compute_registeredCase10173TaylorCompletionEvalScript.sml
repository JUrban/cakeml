(*****************************************************************************
 * Registered evaluator seam for the rounded fixed-scale Taylor completion.
 *
 * This peels the source wrapper down to the two substantive computations:
 * the rounded value enclosure and the rounded gradient enclosures.  The
 * five-field result constructor and all argument plumbing are discharged
 * exactly here, so later object refinement can target those two arithmetic
 * results without replaying the generic evaluator.
 *****************************************************************************)
Theory compute_registeredCase10173TaylorCompletionEval
Ancestors
  compute_registeredCase10173RadiiEval
Libs
  bossLib preamble

Definition registered_case10173_fs_result_make_body_def:
  registered_case10173_fs_result_make_body =
    Pair (Var «domain»)
      (Pair (Var «center»)
        (Pair (Var «value_bound»)
          (Pair (Var «gradient_bounds») (Var «hessian»))))
End

Definition registered_case10173_fs_complete_value_bound_exp_def:
  registered_case10173_fs_complete_value_bound_exp radii center hessian =
    App «candle_cv_fs_raw_interval_round»
      [App «candle_cv_fs_two_scale_squared» [];
       App «candle_cv_fs_raw_interval_add»
        [Pair
          (App «candle_cv_fs_raw_scale»
            [App «candle_cv_fs_two_scale_squared» [];
             Uop Fst (App «candle_cv_fs_first_value» [center])])
          (App «candle_cv_fs_raw_scale»
            [App «candle_cv_fs_two_scale_squared» [];
             Uop Snd (App «candle_cv_fs_first_value» [center])]);
         Pair
          (App «candle_cv_fs_raw_neg»
            [App «candle_cv_fs_raw_add»
              [App «candle_cv_fs_raw_scale»
                [Binop Mul (Num 2) (App «candle_cv_fs_scale» []);
                 App «candle_cv_fs_dot_abs_upper»
                   [radii;App «candle_cv_fs_first_gradient» [center]]];
               App «candle_cv_fs_weighted_rows_abs_upper»
                 [radii;radii;hessian]]])
          (App «candle_cv_fs_raw_add»
            [App «candle_cv_fs_raw_scale»
              [Binop Mul (Num 2) (App «candle_cv_fs_scale» []);
               App «candle_cv_fs_dot_abs_upper»
                 [radii;App «candle_cv_fs_first_gradient» [center]]];
             App «candle_cv_fs_weighted_rows_abs_upper»
               [radii;radii;hessian]])]]
End

Definition registered_case10173_fs_complete_gradient_bounds_exp_def:
  registered_case10173_fs_complete_gradient_bounds_exp radii center hessian =
    App «candle_cv_fs_gradient_bounds»
      [radii;App «candle_cv_fs_first_gradient» [center];hessian]
End

Definition registered_case10173_fs_result_complete_rounded_body_def:
  registered_case10173_fs_result_complete_rounded_body =
    App «candle_cv_fs_result_make»
      [Var «domain»;Var «center»;
       registered_case10173_fs_complete_value_bound_exp
         (Var «radii») (Var «center») (Var «hessian»);
       registered_case10173_fs_complete_gradient_bounds_exp
         (Var «radii») (Var «center») (Var «hessian»);
       Var «hessian»]
End

Theorem registered_case10173_fs_result_make_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_make» =
    SOME
      ([«domain»;«center»;«value_bound»;«gradient_bounds»;«hessian»],
       registered_case10173_fs_result_make_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_complete_rounded_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_complete_rounded» =
    SOME
      ([«radii»;«domain»;«center»;«hessian»],
       registered_case10173_fs_result_complete_rounded_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_compute_eval_app5_argument_results:
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

Theorem registered_case10173_fs_result_make_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_make»
        [from_cv result_domain;from_cv center;from_cv value_bound;
         from_cv gradient_bounds;from_cv hessian])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair result_domain
          (Pair center
            (Pair value_bound (Pair gradient_bounds hessian))))),refs)
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_result_make_lookup,
        registered_case10173_fs_result_make_body_def,
        compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_complete_rounded_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv radii;from_cv result_domain;from_cv center;from_cv hessian])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«radii»,from_cv radii);(«domain»,from_cv result_domain);
         («center»,from_cv center);(«hessian»,from_cv hessian)]
        registered_case10173_fs_result_complete_rounded_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_result_complete_rounded_lookup]
QED

Theorem registered_case10173_fs_result_complete_rounded_body_subst:
  subst
    [(«radii»,from_cv radii);(«domain»,from_cv result_domain);
     («center»,from_cv center);(«hessian»,from_cv hessian)]
    registered_case10173_fs_result_complete_rounded_body =
  App «candle_cv_fs_result_make»
    [from_cv result_domain;from_cv center;
     registered_case10173_fs_complete_value_bound_exp
       (from_cv radii) (from_cv center) (from_cv hessian);
     registered_case10173_fs_complete_gradient_bounds_exp
       (from_cv radii) (from_cv center) (from_cv hessian);
     from_cv hessian]
Proof
  simp
    [registered_case10173_fs_result_complete_rounded_body_def,
     registered_case10173_fs_complete_value_bound_exp_def,
     registered_case10173_fs_complete_gradient_bounds_exp_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fs_result_complete_rounded_eval_from_results:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_complete_value_bound_exp
        (from_cv radii) (from_cv center) (from_cv hessian))
      (refs:hol_refs) =
    (M_success (from_cv value_bound),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (registered_case10173_fs_complete_gradient_bounds_exp
        (from_cv radii) (from_cv center) (from_cv hessian)) refs =
    (M_success (from_cv gradient_bounds),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_complete_rounded»
        [from_cv radii;from_cv result_domain;from_cv center;from_cv hessian]) refs =
    (M_success
      (from_cv
        (Pair result_domain
          (Pair center
            (Pair value_bound (Pair gradient_bounds hessian))))),refs)
Proof
  strip_tac
  >> simp [registered_case10173_fs_result_complete_rounded_unfold]
  >> simp_tac std_ss
       [registered_case10173_fs_result_complete_rounded_body_subst]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_result_make»
          [from_cv result_domain;from_cv center;
           registered_case10173_fs_complete_value_bound_exp
             (from_cv radii) (from_cv center) (from_cv hessian);
           registered_case10173_fs_complete_gradient_bounds_exp
             (from_cv radii) (from_cv center) (from_cv hessian);
           from_cv hessian]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_result_make»
          [from_cv result_domain;from_cv center;from_cv value_bound;
           from_cv gradient_bounds;from_cv hessian]) refs` by
       (irule registered_case10173_compute_eval_app5_argument_results
        >> conj_tac >- intLib.ARITH_TAC
        >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
        >> conj_tac >- simp [compute_execProofTheory.compute_eval_from_cv]
        >> conj_tac >- fs []
        >> conj_tac >- fs []
        >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> fs [registered_case10173_fs_result_make_eval]
QED

val _ = export_theory ();
