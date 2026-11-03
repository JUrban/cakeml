(*****************************************************************************
 * Structural evaluator semantics for the explicit-radius object dispatcher.
 *
 * Numerical operations remain premises.  This layer authenticates the exact
 * generated ordinary and dispatch bodies, then proves their control flow once.
 * The six authenticated specialized branches are added in the next packet.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchStepControlEval
Ancestors
  compute_boundedCase16594ObjectDispatchProgramTraceEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_ordinary_step_body_def:
  bounded_case16594_object_ordinary_step_body =
    If (Uop Ispair (Var «source»))
      (If (Binop Eq (Uop Fst (Var «source»)) (Num 0))
        (Let «execution»
          (App «candle_cv_q_packed_object_poly_run»
            [Var «center_boxes»;Var «outer_boxes»;Var «radii»;
             Uop Snd (Var «source»);Pair (Num 1) (Num 0)])
          (Let «result_stack» (Uop Snd (Var «execution»))
            (If (Uop Fst (Var «execution»))
              (If (Uop Ispair (Var «result_stack»))
                (If (Binop Eq (Uop Snd (Var «result_stack»)) (Num 0))
                  (Pair (Num 1)
                    (Pair
                      (Pair (Uop Fst (Var «result_stack»)) (Var «stack»))
                      (Var «certificates»)))
                  (Pair (Num 0)
                    (Pair (Var «stack») (Var «certificates»))))
                (Pair (Num 0)
                  (Pair (Var «stack») (Var «certificates»))))
              (Pair (Num 0)
                (Pair (Var «stack») (Var «certificates»))))))
        (App «candle_cv_q_packed_object_nonpoly_step»
          [Var «center_boxes»;Var «outer_boxes»;Var «radii»;Var «source»;
           Var «certificates»;Var «stack»]))
      (App «candle_cv_q_packed_object_nonpoly_step»
        [Var «center_boxes»;Var «outer_boxes»;Var «radii»;Var «source»;
         Var «certificates»;Var «stack»])
End

Theorem bounded_case16594_object_ordinary_step_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_ordinary_step» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«source»;«certificates»;
        «stack»],bounded_case16594_object_ordinary_step_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_compute_eval_literal_app6:
  0 < clock /\
  ALOOKUP ceqs function_name =
    SOME ([name1;name2;name3;name4;name5;name6],body) ==>
  compute_eval clock ceqs
      (App function_name
        [from_cv argument1;from_cv argument2;from_cv argument3;
         from_cv argument4;from_cv argument5;from_cv argument6])
      (refs:hol_refs) =
    compute_eval (clock - 1) ceqs
      (subst
        [(name1,from_cv argument1);(name2,from_cv argument2);
         (name3,from_cv argument3);(name4,from_cv argument4);
         (name5,from_cv argument5);(name6,from_cv argument6)] body) refs
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

Theorem bounded_case16594_object_ordinary_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («source»,from_cv source);(«certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_case16594_object_ordinary_step_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app6
  >> simp [bounded_case16594_object_ordinary_step_lookup]
QED

Theorem bounded_case16594_object_compute_eval_if_ispair_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (from_cv left) (from_cv right)))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_if_ispair_num_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (Num tag) (from_cv payload)))
        yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_if_fst_num_pair_eq:
  compute_eval clock ceqs
      (If
        (Binop Eq (Uop Fst (Pair (Num tag) (from_cv payload)))
          (Num expected)) yes_branch no_branch)
      (refs:hol_refs) =
    if tag = expected then compute_eval clock ceqs yes_branch refs
    else compute_eval clock ceqs no_branch refs
Proof
  Cases_on `tag = expected`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_ordinary_nonpair_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num source);from_cv certificates;from_cv stack])
      (refs:hol_refs) = result ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num source);from_cv certificates;from_cv stack]) refs = result
Proof
  strip_tac
  >> rw [bounded_case16594_object_ordinary_step_unfold]
  >> simp
       [bounded_case16594_object_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_ordinary_nonzero_pair_eval:
  tag <> 0 /\ 1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num tag) payload);from_cv certificates;from_cv stack])
      (refs:hol_refs) = result ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num tag) payload);from_cv certificates;from_cv stack])
      refs = result
Proof
  strip_tac
  >> rw [bounded_case16594_object_ordinary_step_unfold]
  >> simp
       [bounded_case16594_object_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_ordinary_poly_success_eval:
  3 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         Uop Snd (from_cv (Pair (Num 0) program));
         Pair (Num 1) (Num 0)])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Num 1) (Pair result_value (Num 0)))),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num 0) program);from_cv certificates;from_cv stack])
      refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_ordinary_step_unfold]
  >> simp
       [bounded_case16594_object_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_ispair_num_pair,
        bounded_case16594_object_compute_eval_if_ispair_pair,
        bounded_case16594_object_compute_eval_if_fst_num_pair_eq]
  >> irule bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Pair (Num 1) (Pair result_value (Num 0))`
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Pair result_value (Num 0)`
  >> conj_tac
  >- simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_snd_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_dispatch_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv code;from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («code»,from_cv code);(«source»,from_cv source);
         («certificates»,from_cv certificates);(«stack»,from_cv stack)]
        bounded_case16594_object_dispatch_step_body) refs
Proof
  strip_tac
  >> irule bounded_case16594_object_compute_eval_literal_app7
  >> simp
       [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_dispatch_step_lookup]
QED

Theorem bounded_case16594_object_dispatch_ordinary_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_ordinary_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) = result ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 0);from_cv source;from_cv certificates;from_cv stack])
      refs = result
Proof
  strip_tac
  >> rw [bounded_case16594_object_dispatch_step_unfold]
  >> simp
       [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_dispatch_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_dispatch_specialized_eval:
  code <> 0 /\ 1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num code);from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) = result ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_dispatch_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num code);from_cv source;from_cv certificates;from_cv stack])
      refs = result
Proof
  strip_tac
  >> rw [bounded_case16594_object_dispatch_step_unfold]
  >> simp
       [compute_boundedCase16594ObjectDispatchCell0ShapeTheory.bounded_case16594_object_dispatch_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

val _ = export_theory ();
