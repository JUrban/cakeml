(*****************************************************************************
 * Structural evaluator semantics for the six authenticated explicit-radius
 * case-16594 delta branches.
 *
 * The source programs are named by positions in the authenticated source cv.
 * The compact body is proved equal to the exact generated Candle body, so an
 * opcode alone or an arbitrary source alias cannot select a specialized path.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectSpecializedStepControlEval
Ancestors
  compute_boundedCase16594ObjectDispatchStepControlEval
  compute_boundedCase16594SourceCVData
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_cv_nth_def:
  bounded_case16594_object_cv_nth 0 (Pair item items) = item /\
  bounded_case16594_object_cv_nth (SUC index) (Pair item items) =
    bounded_case16594_object_cv_nth index items /\
  bounded_case16594_object_cv_nth index (Num nil) = Num nil
End

Definition bounded_case16594_object_source34_cv_def:
  bounded_case16594_object_source34_cv =
    bounded_case16594_object_cv_nth 34 bounded_case16594_source_program_cv
End

Definition bounded_case16594_object_source35_cv_def:
  bounded_case16594_object_source35_cv =
    bounded_case16594_object_cv_nth 35 bounded_case16594_source_program_cv
End

Definition bounded_case16594_object_source77_cv_def:
  bounded_case16594_object_source77_cv =
    bounded_case16594_object_cv_nth 77 bounded_case16594_source_program_cv
End

Definition bounded_case16594_object_source78_cv_def:
  bounded_case16594_object_source78_cv =
    bounded_case16594_object_cv_nth 78 bounded_case16594_source_program_cv
End

Definition bounded_case16594_object_source120_cv_def:
  bounded_case16594_object_source120_cv =
    bounded_case16594_object_cv_nth 120 bounded_case16594_source_program_cv
End

Definition bounded_case16594_object_source121_cv_def:
  bounded_case16594_object_source121_cv =
    bounded_case16594_object_cv_nth 121 bounded_case16594_source_program_cv
End

Definition bounded_case16594_object_specialized_step_compact_body_def:
  bounded_case16594_object_specialized_step_compact_body =
    If (Binop Eq (Var «code») (Num 1))
      (If (Binop Eq (Var «source»)
             (from_cv bounded_case16594_object_source35_cv))
        (Pair (Num 1)
          (Pair
            (Pair
              (App «candle_cv_q_packed_object_delta_product_source_item_state»
                [Var «radii»;Var «center_boxes»;Var «outer_boxes»;Num 0])
              (Var «stack»))
            (Var «certificates»)))
        (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
      (If (Binop Eq (Var «code») (Num 2))
        (If (Binop Eq (Var «source»)
               (from_cv bounded_case16594_object_source78_cv))
          (Pair (Num 1)
            (Pair
              (Pair
                (App «candle_cv_q_packed_object_delta_product_source_item_state»
                  [Var «radii»;Var «center_boxes»;Var «outer_boxes»;Num 1])
                (Var «stack»))
              (Var «certificates»)))
          (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
        (If (Binop Eq (Var «code») (Num 3))
          (If (Binop Eq (Var «source»)
                 (from_cv bounded_case16594_object_source121_cv))
            (Pair (Num 1)
              (Pair
                (Pair
                  (App
                    «candle_cv_q_packed_object_delta_product_source_item_state»
                    [Var «radii»;Var «center_boxes»;Var «outer_boxes»;Num 2])
                  (Var «stack»))
                (Var «certificates»)))
            (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
          (If (Binop Eq (Var «code») (Num 4))
            (If (Binop Eq (Var «source»)
                   (from_cv bounded_case16594_object_source34_cv))
              (Pair (Num 1)
                (Pair
                  (Pair
                    (App
                      «candle_cv_q_packed_object_delta_neg_derivative_item_state»
                      [Var «radii»;Var «center_boxes»;Num 3])
                    (Var «stack»))
                  (Var «certificates»)))
              (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
            (If (Binop Eq (Var «code») (Num 5))
              (If (Binop Eq (Var «source»)
                     (from_cv bounded_case16594_object_source77_cv))
                (Pair (Num 1)
                  (Pair
                    (Pair
                      (App
                        «candle_cv_q_packed_object_delta_neg_derivative_item_state»
                        [Var «radii»;Var «center_boxes»;Num 4])
                      (Var «stack»))
                    (Var «certificates»)))
                (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
              (If (Binop Eq (Var «code») (Num 6))
                (If (Binop Eq (Var «source»)
                       (from_cv bounded_case16594_object_source120_cv))
                  (Pair (Num 1)
                    (Pair
                      (Pair
                        (App
                          «candle_cv_q_packed_object_delta_neg_derivative_item_state»
                          [Var «radii»;Var «center_boxes»;Num 5])
                        (Var «stack»))
                      (Var «certificates»)))
                  (Pair (Num 0) (Pair (Var «stack») (Var «certificates»))))
                (Pair (Num 0)
                  (Pair (Var «stack») (Var «certificates»))))))))
End

Theorem bounded_case16594_object_specialized_step_compact_lookup:
  ALOOKUP bounded_case16594_object_dispatch_cell0_ceqs
      «candle_cv_q_packed_object_specialized_step» =
    SOME
      ([«center_boxes»;«outer_boxes»;«radii»;«code»;«source»;
        «certificates»;«stack»],
       bounded_case16594_object_specialized_step_compact_body)
Proof
  EVAL_TAC
QED

Theorem bounded_case16594_object_specialized_step_compact_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;from_cv code;
         from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_object_dispatch_cell0_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);
         («outer_boxes»,from_cv outer_boxes);(«radii»,from_cv radii);
         («code»,from_cv code);(«source»,from_cv source);
         («certificates»,from_cv certificates);(«stack»,from_cv stack)]
        bounded_case16594_object_specialized_step_compact_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_literal_app7
  >> simp [bounded_case16594_object_specialized_step_compact_lookup]
QED

Theorem bounded_case16594_object_compute_eval_if_num_eq:
  compute_eval clock ceqs
      (If (Binop Eq (Num left) (Num right)) yes_branch no_branch)
      (refs:hol_refs) =
    if left = right then compute_eval clock ceqs yes_branch refs
    else compute_eval clock ceqs no_branch refs
Proof
  Cases_on `left = right`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_if_from_cv_eq:
  compute_eval clock ceqs
      (If (Binop Eq (from_cv left) (from_cv right))
        yes_branch no_branch)
      (refs:hol_refs) =
    if left = right then compute_eval clock ceqs yes_branch refs
    else compute_eval clock ceqs no_branch refs
Proof
  Cases_on `left = right`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_execProofTheory.from_cv_11,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_compute_eval_success_state:
  compute_eval clock ceqs result_expression (refs:hol_refs) =
      (M_success (from_cv result_value),refs) ==>
  compute_eval clock ceqs
      (Pair (Num 1)
        (Pair (Pair result_expression (from_cv stack))
          (from_cv certificates))) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_object_specialized_product0_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;Num 0])
      (refs:hol_refs) = (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 1);
         from_cv bounded_case16594_object_source35_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_specialized_step_compact_unfold]
  >> simp
       [bounded_case16594_object_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_num_eq,
        bounded_case16594_object_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_compute_eval_success_state)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_specialized_product1_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;Num 1])
      (refs:hol_refs) = (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 2);
         from_cv bounded_case16594_object_source78_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_specialized_step_compact_unfold]
  >> simp
       [bounded_case16594_object_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_num_eq,
        bounded_case16594_object_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_compute_eval_success_state)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_specialized_product2_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;Num 2])
      (refs:hol_refs) = (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 3);
         from_cv bounded_case16594_object_source121_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_specialized_step_compact_unfold]
  >> simp
       [bounded_case16594_object_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_num_eq,
        bounded_case16594_object_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_compute_eval_success_state)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_specialized_neg3_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;Num 3])
      (refs:hol_refs) = (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 4);
         from_cv bounded_case16594_object_source34_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_specialized_step_compact_unfold]
  >> simp
       [bounded_case16594_object_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_num_eq,
        bounded_case16594_object_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_compute_eval_success_state)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_specialized_neg4_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;Num 4])
      (refs:hol_refs) = (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 5);
         from_cv bounded_case16594_object_source77_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_specialized_step_compact_unfold]
  >> simp
       [bounded_case16594_object_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_num_eq,
        bounded_case16594_object_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_compute_eval_success_state)
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_object_specialized_neg5_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;Num 5])
      (refs:hol_refs) = (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
      (App «candle_cv_q_packed_object_specialized_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num 6);
         from_cv bounded_case16594_object_source120_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1) (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_object_specialized_step_compact_unfold]
  >> simp
       [bounded_case16594_object_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_object_compute_eval_if_num_eq,
        bounded_case16594_object_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_compute_eval_success_state)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
