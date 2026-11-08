(*****************************************************************************
 * Semantic/evaluator bridge for one production polynomial variable
 * instruction.  This authenticates opcode 1, its index guard, the exact
 * runtime state pushed on the stack, and that state's Taylor semantics.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyVariableStepSemanticEval
Ancestors
  compute_boundedCase16594ObjectVariableStateEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_object_poly_variable_bool_and_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_bool_and» =
    SOME ([«a»;«b»],If (Var «a») (Var «b») (Num 0))
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_poly_step_variable_control_eval:
  variable < 6 /\ 1 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instruction»,from_cv (Pair (Num 1) (Num variable)));
         («stack»,from_cv stack)]
        bounded_case16594_object_poly_step_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (Pair (Num 1)
        (Pair
          (App «candle_cv_q_packed_object_variable_state»
            [from_cv center_boxes;from_cv outer_boxes;Num variable])
          (from_cv stack))) refs
Proof
  strip_tac
  >> simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_body_def,
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
        compute_evalTheory.do_reln_def,
        compute_evalTheory.do_eq_def,
        bounded_case16594_object_poly_variable_bool_and_lookup,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_poly_step_variable_eval_from_state:
  variable < 6 /\ 2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_variable_state»
        [from_cv center_boxes;from_cv outer_boxes;from_cv (Num variable)])
      (refs:hol_refs) = (M_success (from_cv result_state),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num 1) (Num variable));from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Num 1) (Pair result_state stack))),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_poly_step_unfold]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (Pair (Num 1)
            (Pair
              (App «candle_cv_q_packed_object_variable_state»
                [from_cv center_boxes;from_cv outer_boxes;Num variable])
              (from_cv stack))) refs`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          bounded_case16594_object_poly_step_variable_control_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> conj_tac
  >- simp
       [compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_num]
  >> irule
       compute_boundedCase16594ObjectPolyStepControlEvalTheory.bounded_case16594_object_compute_eval_pair_from_raw_results
  >> fs
       [compute_execTheory.from_cv_def,
        compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_case16594_object_poly_step_variable_eval_semantic:
  LENGTH runtime_center_boxes = 6 /\
  LENGTH runtime_outer_boxes = 6 /\
  variable < 6 /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_center_boxes semantic_center_boxes /\
  LIST_REL bounded_object_q_interval_cv_equiv
    runtime_outer_boxes semantic_outer_boxes /\
  59 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_step»
        [from_cv (bounded_object_q_cv_list runtime_center_boxes);
         from_cv (bounded_object_q_cv_list runtime_outer_boxes);
         from_cv radii;
         from_cv (Pair (Num 1) (Num variable));from_cv stack])
      (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair
            (bounded_case16594_object_variable_state_cv
              runtime_center_boxes runtime_outer_boxes variable)
            stack))),refs) /\
  bounded_object_q_taylor_runtime_equiv
    (bounded_case16594_object_variable_state_cv
      runtime_center_boxes runtime_outer_boxes variable)
    (THE
      (bounded_object_q_taylor_variable
        semantic_center_boxes semantic_outer_boxes variable))
Proof
  strip_tac
  >> conj_tac
  >- (irule bounded_case16594_object_poly_step_variable_eval_from_state
      >> simp []
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             bounded_case16594_object_variable_state_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule bounded_case16594_object_variable_state_runtime_semantic_equiv
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
