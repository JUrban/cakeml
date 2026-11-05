(*****************************************************************************
 * Structural evaluator semantics for the six authenticated case-16594 delta
 * branches.
 *
 * The large source programs are named by their positions in the authenticated
 * source-program cv.  The compact body below is proved equal to the generated
 * Candle function body, so no basename, opcode-only, or arbitrary-program
 * alias is accepted.  Numerical result evaluation remains an explicit premise.
 *****************************************************************************)
Theory compute_boundedPackedSourceSpecializedStepControlEval
Ancestors
  compute_boundedPackedSourceOrdinaryStepControlEval
  compute_boundedPackedSourceProgramTraceEval
  compute_boundedCase16594SourceCVData
Libs
  bossLib preamble intLib

Definition bounded_packed_source_cv_nth_def:
  bounded_packed_source_cv_nth 0 (Pair item items) = item /\
  bounded_packed_source_cv_nth (SUC index) (Pair item items) =
    bounded_packed_source_cv_nth index items /\
  bounded_packed_source_cv_nth index (Num nil) = Num nil
End

Definition bounded_case16594_source34_cv_def:
  bounded_case16594_source34_cv =
    bounded_packed_source_cv_nth 34 bounded_case16594_source_program_cv
End

Definition bounded_case16594_source35_cv_def:
  bounded_case16594_source35_cv =
    bounded_packed_source_cv_nth 35 bounded_case16594_source_program_cv
End

Definition bounded_case16594_source77_cv_def:
  bounded_case16594_source77_cv =
    bounded_packed_source_cv_nth 77 bounded_case16594_source_program_cv
End

Definition bounded_case16594_source78_cv_def:
  bounded_case16594_source78_cv =
    bounded_packed_source_cv_nth 78 bounded_case16594_source_program_cv
End

Definition bounded_case16594_source120_cv_def:
  bounded_case16594_source120_cv =
    bounded_packed_source_cv_nth 120 bounded_case16594_source_program_cv
End

Definition bounded_case16594_source121_cv_def:
  bounded_case16594_source121_cv =
    bounded_packed_source_cv_nth 121 bounded_case16594_source_program_cv
End

Definition bounded_packed_source_specialized_step_compact_body_def:
  bounded_packed_source_specialized_step_compact_body =
    If (Binop Eq (Var «code») (Num 1))
      (If (Binop Eq (Var «source»)
             (from_cv bounded_case16594_source35_cv))
        (Pair (Num 1)
          (Pair
            (Pair
              (App «candle_cv_q_packed_delta_product_result»
                [Var «boxes»;Num 0])
              (Var «stack»))
            (Var «certificates»)))
        (App «candle_cv_q_packed_source_certificate_failure»
          [Var «stack»;Var «certificates»]))
      (If (Binop Eq (Var «code») (Num 2))
        (If (Binop Eq (Var «source»)
               (from_cv bounded_case16594_source78_cv))
          (Pair (Num 1)
            (Pair
              (Pair
                (App «candle_cv_q_packed_delta_product_result»
                  [Var «boxes»;Num 1])
                (Var «stack»))
              (Var «certificates»)))
          (App «candle_cv_q_packed_source_certificate_failure»
            [Var «stack»;Var «certificates»]))
        (If (Binop Eq (Var «code») (Num 3))
          (If (Binop Eq (Var «source»)
                 (from_cv bounded_case16594_source121_cv))
            (Pair (Num 1)
              (Pair
                (Pair
                  (App «candle_cv_q_packed_delta_product_result»
                    [Var «boxes»;Num 2])
                  (Var «stack»))
                (Var «certificates»)))
            (App «candle_cv_q_packed_source_certificate_failure»
              [Var «stack»;Var «certificates»]))
          (If (Binop Eq (Var «code») (Num 4))
            (If (Binop Eq (Var «source»)
                   (from_cv bounded_case16594_source34_cv))
              (Pair (Num 1)
                (Pair
                  (Pair
                    (App «candle_cv_q_packed_delta_neg_derivative_result»
                      [Var «boxes»;Num 3])
                    (Var «stack»))
                  (Var «certificates»)))
              (App «candle_cv_q_packed_source_certificate_failure»
                [Var «stack»;Var «certificates»]))
            (If (Binop Eq (Var «code») (Num 5))
              (If (Binop Eq (Var «source»)
                     (from_cv bounded_case16594_source77_cv))
                (Pair (Num 1)
                  (Pair
                    (Pair
                      (App «candle_cv_q_packed_delta_neg_derivative_result»
                        [Var «boxes»;Num 4])
                      (Var «stack»))
                    (Var «certificates»)))
                (App «candle_cv_q_packed_source_certificate_failure»
                  [Var «stack»;Var «certificates»]))
              (If (Binop Eq (Var «code») (Num 6))
                (If (Binop Eq (Var «source»)
                       (from_cv bounded_case16594_source120_cv))
                  (Pair (Num 1)
                    (Pair
                      (Pair
                        (App «candle_cv_q_packed_delta_neg_derivative_result»
                          [Var «boxes»;Num 5])
                        (Var «stack»))
                      (Var «certificates»)))
                  (App «candle_cv_q_packed_source_certificate_failure»
                    [Var «stack»;Var «certificates»]))
                (App «candle_cv_q_packed_source_certificate_failure»
                  [Var «stack»;Var «certificates»]))))))
End

Theorem bounded_packed_source_specialized_step_compact_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_packed_source_certificate_specialized_step» =
    SOME
      ([«boxes»;«code»;«source»;«certificates»;«stack»],
       bounded_packed_source_specialized_step_compact_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_specialized_step_compact_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv code;from_cv source;
         from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst
        [(«boxes»,from_cv boxes);(«code»,from_cv code);
         («source»,from_cv source);
         («certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_packed_source_specialized_step_compact_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app5
  >> simp [bounded_packed_source_specialized_step_compact_lookup]
QED

Theorem bounded_packed_source_compute_eval_if_from_cv_eq:
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

Theorem bounded_packed_source_specialized_product0_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_delta_product_result»
        [from_cv boxes;Num 0]) (refs:hol_refs) =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv (Num 1);
         from_cv bounded_case16594_source35_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_specialized_step_compact_unfold]
  >> simp
       [bounded_packed_source_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_num_eq,
        bounded_packed_source_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> asm_rewrite_tac []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_specialized_product1_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_delta_product_result»
        [from_cv boxes;Num 1]) (refs:hol_refs) =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv (Num 2);
         from_cv bounded_case16594_source78_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_specialized_step_compact_unfold]
  >> simp
       [bounded_packed_source_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_num_eq,
        bounded_packed_source_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> asm_rewrite_tac []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_specialized_product2_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_delta_product_result»
        [from_cv boxes;Num 2]) (refs:hol_refs) =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv (Num 3);
         from_cv bounded_case16594_source121_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_specialized_step_compact_unfold]
  >> simp
       [bounded_packed_source_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_num_eq,
        bounded_packed_source_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> asm_rewrite_tac []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_specialized_neg3_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_result»
        [from_cv boxes;Num 3]) (refs:hol_refs) =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv (Num 4);
         from_cv bounded_case16594_source34_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_specialized_step_compact_unfold]
  >> simp
       [bounded_packed_source_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_num_eq,
        bounded_packed_source_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> asm_rewrite_tac []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_specialized_neg4_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_result»
        [from_cv boxes;Num 4]) (refs:hol_refs) =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv (Num 5);
         from_cv bounded_case16594_source77_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_specialized_step_compact_unfold]
  >> simp
       [bounded_packed_source_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_num_eq,
        bounded_packed_source_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> asm_rewrite_tac []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_specialized_neg5_eval:
  1 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_delta_neg_derivative_result»
        [from_cv boxes;Num 5]) (refs:hol_refs) =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_specialized_step»
        [from_cv boxes;from_cv (Num 6);
         from_cv bounded_case16594_source120_cv;
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_specialized_step_compact_unfold]
  >> simp
       [bounded_packed_source_specialized_step_compact_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_num_eq,
        bounded_packed_source_compute_eval_if_from_cv_eq]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> asm_rewrite_tac []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_specialized_product0_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_delta_product_result»
        [from_cv boxes;Num 0]) result_value ==>
  bounded_packed_source_specialized_step_eval_above (numeric_floor + 1)
      boxes 0 bounded_case16594_source35_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_packed_source_expression_eval_above_def,
      bounded_packed_source_specialized_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_specialized_product0_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_specialized_product1_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_delta_product_result»
        [from_cv boxes;Num 1]) result_value ==>
  bounded_packed_source_specialized_step_eval_above (numeric_floor + 1)
      boxes 1 bounded_case16594_source78_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_packed_source_expression_eval_above_def,
      bounded_packed_source_specialized_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_specialized_product1_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_specialized_product2_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_delta_product_result»
        [from_cv boxes;Num 2]) result_value ==>
  bounded_packed_source_specialized_step_eval_above (numeric_floor + 1)
      boxes 2 bounded_case16594_source121_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_packed_source_expression_eval_above_def,
      bounded_packed_source_specialized_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_specialized_product2_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_specialized_neg3_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_delta_neg_derivative_result»
        [from_cv boxes;Num 3]) result_value ==>
  bounded_packed_source_specialized_step_eval_above (numeric_floor + 1)
      boxes 3 bounded_case16594_source34_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_packed_source_expression_eval_above_def,
      bounded_packed_source_specialized_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_specialized_neg3_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_specialized_neg4_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_delta_neg_derivative_result»
        [from_cv boxes;Num 4]) result_value ==>
  bounded_packed_source_specialized_step_eval_above (numeric_floor + 1)
      boxes 4 bounded_case16594_source77_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_packed_source_expression_eval_above_def,
      bounded_packed_source_specialized_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_specialized_neg4_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_specialized_neg5_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_delta_neg_derivative_result»
        [from_cv boxes;Num 5]) result_value ==>
  bounded_packed_source_specialized_step_eval_above (numeric_floor + 1)
      boxes 5 bounded_case16594_source120_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_packed_source_expression_eval_above_def,
      bounded_packed_source_specialized_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_specialized_neg5_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
