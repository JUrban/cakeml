(*****************************************************************************
 * Structural evaluator trace for the explicit-radius object polynomial run.
 *
 * Numerical state operations remain per-instruction premises.  This theory
 * proves the recursive runner, success-state threading, and clock accounting
 * once, so polynomial programs do not require monolithic evaluator replay.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectPolyTraceEval
Ancestors
  compute_boundedCase16594ObjectDispatchPrefix8Eval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_poly_run_body_def:
  bounded_case16594_object_poly_run_body =
    If (Uop Ispair (Var «instructions»))
      (If (Uop Fst (Var «execution»))
        (App «candle_cv_q_packed_object_poly_run»
          [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
           Uop Snd (Var «instructions»);
           App «candle_cv_q_packed_object_poly_step»
             [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
              Uop Fst (Var «instructions»);Uop Snd (Var «execution»)]])
        (Var «execution»))
      (Var «execution»)
End

Theorem bounded_case16594_object_poly_run_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_poly_run» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«instructions»;
        «execution»],bounded_case16594_object_poly_run_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_poly_run_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv instructions;from_cv execution]) (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instructions»,from_cv instructions);
         («execution»,from_cv execution)]
        bounded_case16594_object_poly_run_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectRecompleteControlEvalTheory.bounded_case16594_object_compute_eval_literal_app5
  >> asm_rewrite_tac [bounded_case16594_object_poly_run_lookup]
QED

Theorem bounded_case16594_object_compute_eval_app5_argument_results:
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

Theorem bounded_case16594_object_poly_run_nil_control_eval:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instructions»,from_cv (Num nil));
         («execution»,from_cv execution)]
        bounded_case16594_object_poly_run_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (from_cv execution) refs
Proof
  simp
    [bounded_case16594_object_poly_run_body_def,
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

Theorem bounded_case16594_object_poly_run_cons_success_control_eval:
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («instructions»,from_cv (Pair instruction rest));
         («execution»,from_cv (Pair (Num 1) stack))]
        bounded_case16594_object_poly_run_body) (refs:hol_refs) =
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;from_cv rest;
         App «candle_cv_q_packed_object_poly_step»
           [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
            from_cv instruction;from_cv stack]]) refs
Proof
  simp
    [bounded_case16594_object_poly_run_body_def,
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

Theorem bounded_case16594_object_poly_run_nil_eval:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num nil);from_cv execution]) (refs:hol_refs) =
    (M_success (from_cv execution),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);
             («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
             («instructions»,from_cv (Num nil));
             («execution»,from_cv execution)]
            bounded_case16594_object_poly_run_body) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_poly_run_unfold
      >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC [bounded_case16594_object_poly_run_nil_control_eval]
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Definition bounded_case16594_object_poly_step_eval_above_def:
  bounded_case16594_object_poly_step_eval_above step_floor
      center_boxes outer_boxes radii instruction stack next_stack <=>
    !clock refs.
      step_floor < clock ==>
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        (App «candle_cv_q_packed_object_poly_step»
          [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
           from_cv instruction;from_cv stack]) (refs:hol_refs) =
        (M_success (from_cv (Pair (Num 1) next_stack)),refs)
End

Definition bounded_case16594_object_poly_program_trace_def:
  (bounded_case16594_object_poly_program_trace step_floor
      center_boxes outer_boxes radii (Num nil) stack final_stack <=>
        final_stack = stack) /\
  (bounded_case16594_object_poly_program_trace step_floor
      center_boxes outer_boxes radii (Pair instruction instructions)
      stack final_stack <=>
        ?next_stack.
          bounded_case16594_object_poly_step_eval_above step_floor
            center_boxes outer_boxes radii instruction stack next_stack /\
          bounded_case16594_object_poly_program_trace step_floor
            center_boxes outer_boxes radii instructions next_stack
            final_stack)
End

Theorem bounded_case16594_object_poly_program_trace_sound:
  !instructions stack final_stack clock refs.
    bounded_case16594_object_poly_program_trace step_floor
      center_boxes outer_boxes radii instructions stack final_stack /\
    step_floor + bounded_case16594_object_cv_list_length instructions + 1 <
      clock ==>
    compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv instructions;from_cv (Pair (Num 1) stack)])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) final_stack)),refs)
Proof
  Induct_on `instructions`
  >- (rpt gen_tac
      >> simp
           [bounded_case16594_object_poly_program_trace_def,
            compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`execution` |-> `Pair (Num 1) stack`,
                `nil` |-> `n`]
               bounded_case16594_object_poly_run_nil_eval))
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> simp
       [bounded_case16594_object_poly_program_trace_def,
        compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_cv_list_length_def]
  >> strip_tac
  (* Pair induction supplies an irrelevant induction hypothesis for the head. *)
  >> last_x_assum kall_tac
  >> sg `0 < clock` >- intLib.ARITH_TAC
  >> PURE_ONCE_REWRITE_TAC
       [MATCH_MP
          (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
            (Q.INST
              [`instructions` |-> `Pair instructions instructions'`,
               `execution` |-> `Pair (Num 1) stack`]
              bounded_case16594_object_poly_run_unfold))
          (ASSUME ``0:num < clock``)]
  >> PURE_ONCE_REWRITE_TAC
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`instruction` |-> `instructions`,
             `rest` |-> `instructions'`]
            bounded_case16594_object_poly_run_cons_success_control_eval)]
  >> sg
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_poly_step»
            [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
             from_cv instructions;from_cv stack]) (refs:hol_refs) =
        (M_success (from_cv (Pair (Num 1) next_stack)),refs)`
  >- (qpat_x_assum
        `bounded_case16594_object_poly_step_eval_above step_floor
           center_boxes outer_boxes radii instructions stack next_stack`
        (fn th =>
          irule
            (REWRITE_RULE
              [bounded_case16594_object_poly_step_eval_above_def] th))
      >> intLib.ARITH_TAC)
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_object_dispatch_cell0_ceqs
          (App «candle_cv_q_packed_object_poly_run»
            [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
             from_cv instructions';from_cv (Pair (Num 1) next_stack)]) refs`
  >> conj_tac
  >- (irule bounded_case16594_object_compute_eval_app5_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv])
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> last_x_assum
       (fn th =>
         irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.SPECL
               [`next_stack`,`final_stack`,`clock - 1`,`refs`] th)))
  >> conj_tac >- intLib.ARITH_TAC
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
