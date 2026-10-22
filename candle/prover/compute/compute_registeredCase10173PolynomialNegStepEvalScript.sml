(*****************************************************************************
 * Registered negation instruction for literal polynomial programs.
 *
 * This lifts the decimal Taylor-result negation contract to the clock-uniform
 * interface and proves the unchanged postfix runner's Num 2 stack step.
 *****************************************************************************)
Theory compute_registeredCase10173PolynomialNegStepEval
Ancestors
  compute_registeredCase10173ResultNegEval
  compute_registeredCase10173PolynomialMulStepEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_result_neg_object_eval_above:
  bounded_hessian64_rows source_hessian = SOME source_rows /\
  bounded_object_fs_taylor_complete radii T
      (bounded_interval64_neg center_value)
      (bounded_interval64_list_neg center_gradient)
      (bounded_interval64_list_neg source_hessian)
      (MAP bounded_interval64_list_neg source_rows) = SOME result /\
  LENGTH radii = 6 /\
  LENGTH center_gradient = 6 /\
  LENGTH source_rows = 6 /\
  SUM (MAP LENGTH source_rows) = 36 /\
  8192 <= numeric_floor ==>
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_neg»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv
           (Pair (Num 1)
             (Pair
               (Pair (bounded_interval64_object_cv center_value)
                 (bounded_interval64_object_cv_list center_gradient))
               (Pair value_bound
                 (Pair gradient_bounds
                   (bounded_interval64_object_cv_matrix source_rows)))))])
      result
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173ResultNegEvalTheory.registered_case10173_fs_result_neg_object_eval)
  >> asm_rewrite_tac []
  >> conj_tac >- fs [arithmeticTheory.LESS_EQ]
  >> conj_tac >- fs [arithmeticTheory.LESS_EQ]
  >> conj_tac >- fs [arithmeticTheory.LESS_EQ]
  >> conj_tac >- fs [arithmeticTheory.LESS_EQ]
  >> conj_tac >- fs [arithmeticTheory.LESS_EQ]
  >> qexists_tac `source_hessian`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_taylor_neg_decimal_eval_above:
  bounded_hessian64_rows source_hessian = SOME source_rows /\
  bounded_taylor64_complete_decimal radii T
      (bounded_interval64_neg center_value)
      (bounded_interval64_list_neg center_gradient)
      (bounded_interval64_list_neg source_hessian) = SOME completed /\
  LENGTH radii = 6 /\
  LENGTH center_gradient = 6 /\
  LENGTH source_rows = 6 /\
  SUM (MAP LENGTH source_rows) = 36 /\
  8192 <= numeric_floor ==>
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_neg»
        [from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv
           (bounded_taylor64_rows_object_cv
             (BoundedTaylor64 T center_value center_gradient
               value_bound gradient_bounds source_hessian)
             source_rows)])
      (bounded_taylor64_rows_object_cv completed
        (MAP bounded_interval64_list_neg source_rows))
Proof
  strip_tac
  >> `bounded_hessian64_rows
        (bounded_interval64_list_neg source_hessian) =
      SOME (MAP bounded_interval64_list_neg source_rows)` by
       (irule
          compute_registeredCase10173ResultNegEvalTheory.registered_case10173_bounded_hessian64_rows_neg
        >> asm_rewrite_tac [])
  >> `bounded_object_fs_taylor_complete radii T
        (bounded_interval64_neg center_value)
        (bounded_interval64_list_neg center_gradient)
        (bounded_interval64_list_neg source_hessian)
        (MAP bounded_interval64_list_neg source_rows) =
      SOME
        (bounded_taylor64_rows_object_cv completed
          (MAP bounded_interval64_list_neg source_rows))` by
       (irule
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact
        >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_taylor64_rows_object_cv_def,
        compute_boundedObjectTaylorCompleteDecimalTheory.bounded_bool_object_cv_def,
        COND_CLAUSES]
  >> irule registered_case10173_fs_result_neg_object_eval_above
  >> asm_rewrite_tac []
  >> qexists_tac `source_hessian`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_poly_step_neg_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («instruction»,from_cv (Num 2));
         («stack»,from_cv
           (Pair (value:cv) (stack_tail:cv) : cv))]
        registered_case10173_fs_poly_step_body)
      (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Pair
        (App «candle_cv_fs_result_neg»
          [from_cv radii;
           App «candle_cv_fs_result_head»
             [from_cv dimensions;
              from_cv (Pair (value:cv) (stack_tail:cv) : cv)]])
        (App «candle_cv_fs_result_tail»
          [from_cv (Pair (value:cv) (stack_tail:cv) : cv)])) refs
Proof
  simp
    [compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_step_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_poly_step_neg_eval_from_result:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_neg»
        [from_cv radii;from_cv value]) (refs:hol_refs) =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_step»
        [from_cv dimensions;from_cv radii;from_cv (Num 2);
         from_cv (Pair (value:cv) (stack_tail:cv) : cv)]) refs =
    (M_success
      (from_cv (Pair (result:cv) (stack_tail:cv) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («instruction»,from_cv (Num 2));
             («stack»,from_cv
               (Pair (value:cv) (stack_tail:cv) : cv))]
            registered_case10173_fs_poly_step_body) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_step_neg_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_result_neg»
                [from_cv radii;from_cv value]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> irule
               compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_result_head_cons_eval
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173PolynomialMulStepEvalTheory.registered_case10173_fs_result_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_poly_neg_step_eval_above:
  registered_case10173_eval_above result_floor
      (App «candle_cv_fs_result_neg»
        [from_cv radii;from_cv value]) result ==>
  registered_case10173_poly_step_eval_above (result_floor + 2)
      dimensions radii (Num 2)
      (Pair value stack_tail)
      (Pair result stack_tail)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_poly_step_neg_eval_from_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> fs
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
