(*****************************************************************************
 * Compositional registered semantics for the literal polynomial runner.
 *
 * The case-10173 source prefix repeatedly calls fs_poly_program on short,
 * fixed postfix programs.  This layer threads clock-uniform instruction
 * contracts through the unchanged fs_poly_run recursion and its two wrapper
 * functions.  Later coefficient and constant-term proofs therefore need to
 * prove only their constant/negation/multiplication operations, not replay
 * the runner and source-conversion plumbing for every program and packet.
 *****************************************************************************)
Theory compute_registeredCase10173PolynomialTraceEval
Ancestors
  compute_registeredCase10173ActualVariableProgramEval
  compute_registeredCase10173ResultConstantEval
  compute_registeredCase10173OrdinaryStepAboveEval
Libs
  bossLib preamble intLib

Definition registered_case10173_poly_step_eval_above_def:
  registered_case10173_poly_step_eval_above step_floor dimensions radii
      instruction stack next_stack <=>
    !clock refs.
      step_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fs_poly_step»
          [from_cv dimensions;from_cv radii;from_cv instruction;
           from_cv stack]) (refs:hol_refs) =
        (M_success (from_cv next_stack),refs)
End

Definition registered_case10173_poly_program_trace_def:
  (registered_case10173_poly_program_trace step_floor dimensions radii
      (Num nil) stack final_stack <=> final_stack = stack) /\
  (registered_case10173_poly_program_trace step_floor dimensions radii
      (Pair instruction program) stack final_stack <=>
        ?next_stack.
          registered_case10173_poly_step_eval_above step_floor dimensions
            radii instruction stack next_stack /\
          registered_case10173_poly_program_trace step_floor dimensions
            radii program next_stack final_stack)
End

Theorem registered_case10173_fs_poly_run_num_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («program»,from_cv (Num nil));(«stack»,from_cv stack)]
        registered_case10173_fs_poly_run_body)
      (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (from_cv stack) refs
Proof
  simp
    [compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_run_body_def,
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

Theorem registered_case10173_fs_poly_run_num_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_run»
        [from_cv dimensions;from_cv radii;from_cv (Num nil);from_cv stack])
      (refs:hol_refs) = (M_success (from_cv stack),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («program»,from_cv (Num nil));(«stack»,from_cv stack)]
            registered_case10173_fs_poly_run_body)
          refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_run_unfold
      >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_run_num_control_eval]
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_poly_program_trace_sound:
  !program stack final_stack clock refs.
    registered_case10173_poly_program_trace step_floor dimensions radii
      program stack final_stack /\
    step_floor + registered_case10173_cv_list_length program + 1 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_run»
        [from_cv dimensions;from_cv radii;from_cv program;from_cv stack])
      (refs:hol_refs) = (M_success (from_cv final_stack),refs)
Proof
  Induct_on `program`
  >- (rpt gen_tac
      >> simp
           [registered_case10173_poly_program_trace_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> strip_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_poly_run_num_eval)
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> simp
       [registered_case10173_poly_program_trace_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («program»,Pair (from_cv program) (from_cv program'));
             («stack»,from_cv stack)]
            registered_case10173_fs_poly_run_body)
          refs`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`program` |-> `Pair program program'`]
            compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_run_unfold))
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`instruction` |-> `program`, `rest` |-> `program'`]
            compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_run_cons_control_eval)]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_poly_run»
            [from_cv dimensions;from_cv radii;from_cv program';
             from_cv next_stack]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> fs [registered_case10173_poly_step_eval_above_def]
      >> first_x_assum match_mp_tac
      >> intLib.ARITH_TAC)
  >> first_x_assum match_mp_tac
  >> conj_tac >- asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_poly_step_constant_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («instruction»,from_cv (Pair (Num 0) encoded));
         («stack»,from_cv stack)]
        registered_case10173_fs_poly_step_body)
      (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Pair
        (App «candle_cv_fs_result_constant»
          [from_cv dimensions;from_cv radii;from_cv encoded])
        (from_cv stack)) refs
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
     compute_evalTheory.do_fst_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_poly_constant_step_eval_above:
  registered_case10173_eval_above result_floor
      (App «candle_cv_fs_result_constant»
        [from_cv dimensions;from_cv radii;from_cv encoded]) result ==>
  registered_case10173_poly_step_eval_above (result_floor + 2)
      dimensions radii (Pair (Num 0) encoded) stack (Pair result stack)
Proof
  strip_tac
  >> simp [registered_case10173_poly_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («instruction»,Pair (Num 0) (from_cv encoded));
             («stack»,from_cv stack)]
            registered_case10173_fs_poly_step_body)
          refs`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST [`instruction` |-> `Pair (Num 0) encoded`]
            compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_step_unfold))
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_poly_step_constant_control_eval]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results)
  >> conj_tac
  >- (fs
        [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
      >> first_x_assum match_mp_tac
      >> intLib.ARITH_TAC)
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_fs_result_constant_object_eval_above:
  bounded_object_q_constant_interval64_decimal encoded = SOME value /\
  zero_rows =
    REPLICATE (LENGTH dimensions)
      (REPLICATE (LENGTH dimensions) bounded_interval64_zero) /\
  bounded_hessian64_rows (bounded_interval64_zeros 21) = SOME zero_rows /\
  bounded_object_fs_taylor_complete radii T value
      (REPLICATE (LENGTH dimensions) bounded_interval64_zero)
      (bounded_interval64_zeros 21) zero_rows = SOME result /\
  3 <= numeric_floor /\
  12 <= numeric_floor /\
  4 * (LENGTH dimensions + 1) + 2 <= numeric_floor /\
  4 * (2 * LENGTH dimensions + 2) + 2 <= numeric_floor /\
  256 *
      (2 * LENGTH radii + LENGTH zero_rows + LENGTH dimensions + 2) + 2 <=
    numeric_floor ==>
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_constant»
        [from_cv (bounded_interval64_object_cv_list dimensions);
         from_cv (registered_case10173_word64_object_cv_list radii);
         from_cv encoded]) result
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> qpat_x_assum
       `zero_rows =
          REPLICATE (LENGTH dimensions)
            (REPLICATE (LENGTH dimensions) bounded_interval64_zero)`
       SUBST_ALL_TAC
  >> irule
       compute_registeredCase10173ResultConstantEvalTheory.registered_case10173_fs_result_constant_object_eval
  >> asm_rewrite_tac []
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `value`
  >> qexists_tac
       `REPLICATE (LENGTH dimensions)
          (REPLICATE (LENGTH dimensions) bounded_interval64_zero)`
  >> asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_poly_program_fixed_eval_above_from_trace:
  registered_case10173_poly_program_trace step_floor dimensions radii
      program (Num 0) (Pair result (Num 0)) ==>
  registered_case10173_eval_above
      (step_floor + registered_case10173_cv_list_length program + 5)
      (App «candle_cv_fs_poly_program_fixed»
        [from_cv dimensions;from_cv radii;from_cv program]) result
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («program»,from_cv program)]
            registered_case10173_fs_poly_program_fixed_body)
          refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_program_fixed_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_program_fixed_control_eval]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_head»
            [from_cv dimensions;from_cv (Pair result (Num 0))]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`stack` |-> `Num 0`,
                `final_stack` |-> `Pair result (Num 0)`]
               (SPEC_ALL registered_case10173_poly_program_trace_sound)))
      >> qexists_tac `step_floor`
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_result_head_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_poly_program_eval_above_from_trace:
  registered_case10173_eval_above conversion_floor
      (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
      dimensions /\
  registered_case10173_eval_above conversion_floor
      (App «candle_cv_fs_list_of_q» [from_cv source_radii]) radii /\
  registered_case10173_poly_program_trace step_floor dimensions radii
      program (Num 0) (Pair result (Num 0)) /\
  conversion_floor <= numeric_floor /\
  step_floor + registered_case10173_cv_list_length program + 5 <=
    numeric_floor ==>
  registered_case10173_eval_above (numeric_floor + 2)
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv source_radii;from_cv program]) result
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);
             («radii»,from_cv source_radii);(«program»,from_cv program)]
            registered_case10173_fs_poly_program_body)
          refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_program_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_program_control_eval]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_poly_program_fixed»
            [from_cv dimensions;from_cv radii;from_cv program]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- (fs
            [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
          >> first_x_assum match_mp_tac
          >> intLib.ARITH_TAC)
      >> conj_tac
      >- (fs
            [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
          >> first_x_assum match_mp_tac
          >> intLib.ARITH_TAC)
      >> irule compute_execProofTheory.compute_eval_from_cv)
  >> drule registered_case10173_poly_program_fixed_eval_above_from_trace
  >> strip_tac
  >> fs
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
QED

val _ = export_theory ();
