(*****************************************************************************
 * Registered evaluation of a one-instruction coordinate polynomial.
 *
 * The actual-operand contract already proves the literal result-variable
 * call.  The unchanged source, however, reaches that call through
 * fs_poly_program, its fixed wrapper, the one-step polynomial runner, and
 * result_head.  This theory proves that small source wrapper once without
 * replaying the numerical Taylor calculation.
 *****************************************************************************)
Theory compute_registeredCase10173ActualVariableProgramEval
Ancestors
  compute_registeredCase10173ActualVariableEval
  compute_registeredCase10173QConversionEval
  compute_registeredCase10173RadiiEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_head_body_def:
  registered_case10173_fs_result_head_body =
    If (Uop Ispair (Var «stack»))
      (Uop Fst (Var «stack»))
      (App «candle_cv_fs_result_zero» [Var «dimensions»])
End

Definition registered_case10173_fs_poly_step_body_def:
  registered_case10173_fs_poly_step_body =
    If (Uop Ispair (Var «instruction»))
      (If (Binop Eq (Uop Fst (Var «instruction»)) (Num 0))
        (Pair
          (App «candle_cv_fs_result_constant»
            [Var «dimensions»;Var «radii»;
             Uop Snd (Var «instruction»)])
          (Var «stack»))
        (Pair
          (App «candle_cv_fs_result_variable»
            [Var «dimensions»;Var «radii»;
             Uop Snd (Var «instruction»)])
          (Var «stack»)))
      (If (Binop Eq (Var «instruction») (Num 2))
        (Pair
          (App «candle_cv_fs_result_neg»
            [Var «radii»;
             App «candle_cv_fs_result_head»
               [Var «dimensions»;Var «stack»]])
          (App «candle_cv_fs_result_tail» [Var «stack»]))
        (If (Binop Eq (Var «instruction») (Num 3))
          (Pair
            (App «candle_cv_fs_result_add»
              [Var «radii»;
               App «candle_cv_fs_result_head»
                 [Var «dimensions»;
                  App «candle_cv_fs_result_tail» [Var «stack»]];
               App «candle_cv_fs_result_head»
                 [Var «dimensions»;Var «stack»]])
            (App «candle_cv_fs_result_tail»
              [App «candle_cv_fs_result_tail» [Var «stack»]]))
          (If (Binop Eq (Var «instruction») (Num 4))
            (Pair
              (App «candle_cv_fs_result_mul»
                [Var «radii»;
                 App «candle_cv_fs_result_head»
                   [Var «dimensions»;
                    App «candle_cv_fs_result_tail» [Var «stack»]];
                 App «candle_cv_fs_result_head»
                   [Var «dimensions»;Var «stack»]])
              (App «candle_cv_fs_result_tail»
                [App «candle_cv_fs_result_tail» [Var «stack»]]))
            (Pair
              (App «candle_cv_fs_result_square»
                [Var «radii»;
                 App «candle_cv_fs_result_head»
                   [Var «dimensions»;Var «stack»]])
              (App «candle_cv_fs_result_tail» [Var «stack»])))))
End

Definition registered_case10173_fs_poly_run_body_def:
  registered_case10173_fs_poly_run_body =
    If (Uop Ispair (Var «program»))
      (App «candle_cv_fs_poly_run»
        [Var «dimensions»;Var «radii»;Uop Snd (Var «program»);
         App «candle_cv_fs_poly_step»
           [Var «dimensions»;Var «radii»;
            Uop Fst (Var «program»);Var «stack»]])
      (Var «stack»)
End

Definition registered_case10173_fs_poly_program_fixed_body_def:
  registered_case10173_fs_poly_program_fixed_body =
    App «candle_cv_fs_result_head»
      [Var «dimensions»;
       App «candle_cv_fs_poly_run»
         [Var «dimensions»;Var «radii»;Var «program»;Num 0]]
End

Definition registered_case10173_fs_poly_program_body_def:
  registered_case10173_fs_poly_program_body =
    App «candle_cv_fs_poly_program_fixed»
      [App «candle_cv_fs_interval_list_of_q» [Var «center_boxes»];
       App «candle_cv_fs_list_of_q» [Var «radii»];
       Var «program»]
End

Theorem registered_case10173_fs_result_head_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_head» =
    SOME
      ([«dimensions»;«stack»],
       registered_case10173_fs_result_head_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_poly_step_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_poly_step» =
    SOME
      ([«dimensions»;«radii»;«instruction»;«stack»],
       registered_case10173_fs_poly_step_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_poly_run_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_poly_run» =
    SOME
      ([«dimensions»;«radii»;«program»;«stack»],
       registered_case10173_fs_poly_run_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_poly_program_fixed_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_poly_program_fixed» =
    SOME
      ([«dimensions»;«radii»;«program»],
       registered_case10173_fs_poly_program_fixed_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_poly_program_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_poly_program» =
    SOME
      ([«center_boxes»;«radii»;«program»],
       registered_case10173_fs_poly_program_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_head_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_head»
        [from_cv dimensions;from_cv stack]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«stack»,from_cv stack)]
        registered_case10173_fs_result_head_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173AnalyticSqrtEvalTheory.compute_eval_literal_app2
  >> simp [registered_case10173_fs_result_head_lookup]
QED

Theorem registered_case10173_fs_poly_step_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_step»
        [from_cv dimensions;from_cv radii;from_cv instruction;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («instruction»,from_cv instruction);(«stack»,from_cv stack)]
        registered_case10173_fs_poly_step_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_poly_step_lookup]
QED

Theorem registered_case10173_fs_poly_run_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_run»
        [from_cv dimensions;from_cv radii;from_cv program;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («program»,from_cv program);(«stack»,from_cv stack)]
        registered_case10173_fs_poly_run_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CertifiedCheckEvalTheory.registered_case10173_compute_eval_literal_app4
  >> simp [registered_case10173_fs_poly_run_lookup]
QED

Theorem registered_case10173_fs_poly_program_fixed_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_program_fixed»
        [from_cv dimensions;from_cv radii;from_cv program])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («program»,from_cv program)]
        registered_case10173_fs_poly_program_fixed_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_poly_program_fixed_lookup]
QED

Theorem registered_case10173_fs_poly_program_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv program])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«radii»,from_cv radii);
         («program»,from_cv program)]
        registered_case10173_fs_poly_program_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173TaylorWeightedRowsEvalTheory.registered_case10173_compute_eval_literal_app3
  >> simp [registered_case10173_fs_poly_program_lookup]
QED

Theorem registered_case10173_fs_poly_step_variable_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («instruction»,from_cv (Pair (Num 1) (Num variable)));
         («stack»,from_cv (Num 0))]
        registered_case10173_fs_poly_step_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Pair
        (App «candle_cv_fs_result_variable»
          [from_cv dimensions;from_cv radii;Num variable])
        (from_cv (Num 0))) refs
Proof
  simp
    [registered_case10173_fs_poly_step_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.option_def,
     compute_evalTheory.check_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_poly_run_cons_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («program»,from_cv (Pair instruction rest));
         («stack»,from_cv stack)]
        registered_case10173_fs_poly_run_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_run»
        [from_cv dimensions;from_cv radii;from_cv rest;
         App «candle_cv_fs_poly_step»
           [from_cv dimensions;from_cv radii;from_cv instruction;
            from_cv stack]]) refs
Proof
  simp
    [registered_case10173_fs_poly_run_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_poly_run_nil_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («program»,from_cv (Num 0));(«stack»,from_cv stack)]
        registered_case10173_fs_poly_run_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (from_cv stack) refs
Proof
  simp
    [registered_case10173_fs_poly_run_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_head_cons_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);
         («stack»,
          from_cv (Pair (stack_head:cv) (stack_tail:cv) : cv))]
        registered_case10173_fs_result_head_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (from_cv (stack_head:cv)) refs
Proof
  simp
    [registered_case10173_fs_result_head_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_fst_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_poly_program_fixed_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («program»,from_cv program)]
        registered_case10173_fs_poly_program_fixed_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_head»
        [from_cv dimensions;
         App «candle_cv_fs_poly_run»
           [from_cv dimensions;from_cv radii;from_cv program;
            from_cv (Num 0)]]) refs
Proof
  simp
    [registered_case10173_fs_poly_program_fixed_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fs_poly_program_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«radii»,from_cv radii);
         («program»,from_cv program)]
        registered_case10173_fs_poly_program_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_program_fixed»
        [App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes];
         App «candle_cv_fs_list_of_q» [from_cv radii];
         from_cv program]) refs
Proof
  simp
    [registered_case10173_fs_poly_program_body_def,
     compute_evalTheory.subst_def]
QED

Theorem registered_case10173_fs_poly_run_nil_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_run»
        [from_cv dimensions;from_cv radii;from_cv (Num 0);from_cv stack])
      (refs:hol_refs) =
    (M_success (from_cv stack),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («program»,from_cv (Num 0));(«stack»,from_cv stack)]
            registered_case10173_fs_poly_run_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_poly_run_unfold
      >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_run_nil_control_eval]
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_fs_result_head_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_head»
        [from_cv dimensions;
         from_cv (Pair (stack_head:cv) (stack_tail:cv) : cv)])
      (refs:hol_refs) =
    (M_success (from_cv (stack_head:cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);
             («stack»,
              from_cv (Pair (stack_head:cv) (stack_tail:cv) : cv))]
            registered_case10173_fs_result_head_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_result_head_unfold
      >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC [registered_case10173_fs_result_head_cons_control_eval]
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_actual_variable_poly_step_eval:
  LENGTH radii = 6 /\
  LENGTH dimensions = 6 /\
  variable < 6 /\
  zero_rows = REPLICATE 6 (REPLICATE 6 bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_case10173_actual_variable_decimal radii dimensions variable =
    SOME result /\
  8196 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_step»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (Pair (Num 1) (Num variable));from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (bounded_taylor64_rows_object_cv result zero_rows)
                       (Num 0))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,
              from_cv (bounded_interval64_object_cv_list dimensions));
             («radii»,
              from_cv (registered_case10173_word64_object_cv_list radii));
             («instruction»,from_cv (Pair (Num 1) (Num variable)));
             («stack»,from_cv (Num 0))]
            registered_case10173_fs_poly_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_poly_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fs_poly_step_variable_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualVariableEvalTheory.registered_case10173_actual_variable_object_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_actual_variable_poly_run_eval:
  LENGTH radii = 6 /\
  LENGTH dimensions = 6 /\
  variable < 6 /\
  zero_rows = REPLICATE 6 (REPLICATE 6 bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_case10173_actual_variable_decimal radii dimensions variable =
    SOME result /\
  8200 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_run»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0));
         from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair (bounded_taylor64_rows_object_cv result zero_rows)
                     (Num 0))),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,
              from_cv (bounded_interval64_object_cv_list dimensions));
             («radii»,
              from_cv (registered_case10173_word64_object_cv_list radii));
             («program»,
              from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0)));
             («stack»,from_cv (Num 0))]
            registered_case10173_fs_poly_run_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_poly_run_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_run_cons_control_eval]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_poly_run»
            [from_cv (bounded_interval64_object_cv_list dimensions);
             from_cv (registered_case10173_word64_object_cv_list radii);
             from_cv (Num 0);
             from_cv
               (Pair (bounded_taylor64_rows_object_cv result zero_rows)
                 (Num 0))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_actual_variable_poly_step_eval)
      >> asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)`
      >> simp [])
  >> irule registered_case10173_fs_poly_run_nil_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_actual_variable_poly_program_fixed_eval:
  LENGTH radii = 6 /\
  LENGTH dimensions = 6 /\
  variable < 6 /\
  zero_rows = REPLICATE 6 (REPLICATE 6 bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_case10173_actual_variable_decimal radii dimensions variable =
    SOME result /\
  8204 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_program_fixed»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0))])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_taylor64_rows_object_cv result zero_rows)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,
              from_cv (bounded_interval64_object_cv_list dimensions));
             («radii»,
              from_cv (registered_case10173_word64_object_cv_list radii));
             («program»,
              from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0)))]
            registered_case10173_fs_poly_program_fixed_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_poly_program_fixed_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_program_fixed_control_eval]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_head»
            [from_cv (bounded_interval64_object_cv_list dimensions);
             from_cv
               (Pair (bounded_taylor64_rows_object_cv result zero_rows)
                 (Num 0))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_actual_variable_poly_run_eval)
      >> asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `REPLICATE 6 (REPLICATE 6 bounded_interval64_zero)`
      >> simp [])
  >> irule registered_case10173_fs_result_head_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_actual_variable_poly_program_eval:
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME dimensions /\
  LENGTH radii = 6 /\
  LENGTH dimensions = 6 /\
  variable < 6 /\
  zero_rows = REPLICATE 6 (REPLICATE 6 bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_case10173_actual_variable_decimal radii dimensions variable =
    SOME result /\
  (!clock refs.
    8208 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_list_of_q» [from_cv source_radii])
      (refs:hol_refs) =
    (M_success
      (from_cv (registered_case10173_word64_object_cv_list radii)),refs)) ==>
  !clock refs.
    8209 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;
         from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0))])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_taylor64_rows_object_cv result zero_rows)),refs)
Proof
  strip_tac
  >> rpt gen_tac
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);
             («radii»,from_cv source_radii);
             («program»,
              from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0)))]
            registered_case10173_fs_poly_program_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_poly_program_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_program_control_eval]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_poly_program_fixed»
            [from_cv (bounded_interval64_object_cv_list dimensions);
             from_cv (registered_case10173_word64_object_cv_list radii);
             from_cv (Pair (Pair (Num 1) (Num variable)) (Num 0))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (irule
            compute_registeredCase10173QConversionEvalTheory.registered_case10173_fs_interval_list_of_q_object_eval
          >> asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> conj_tac
      >- (last_x_assum match_mp_tac
          >> intLib.ARITH_TAC)
      >> irule compute_execProofTheory.compute_eval_from_cv)
  >> irule registered_case10173_actual_variable_poly_program_fixed_eval
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
