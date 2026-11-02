(*****************************************************************************
 * Structural evaluator semantics for one ordinary packed-source instruction.
 *
 * Numerical operations remain premises.  This layer proves only the exact
 * instruction dispatch, stack shape, certificate threading and result shape
 * used by the current complete case-16594 source entry.
 *****************************************************************************)
Theory compute_boundedPackedSourceOrdinaryStepControlEval
Ancestors
  compute_boundedPackedSourceProgramTraceEval
Libs
  bossLib preamble intLib

Definition bounded_packed_source_ordinary_step_body_def:
  bounded_packed_source_ordinary_step_body =
    Let «radii»
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [Var «boxes»]])
      (If (Uop Ispair (Var «source»))
        (If (Binop Eq (Uop Fst (Var «source»)) (Num 0))
          (Pair (Num 1)
            (Pair
              (Pair
                (App «candle_cv_q_dim_taylor_model_poly_program»
                  [App «candle_cv_q_center_environment_list»
                     [Var «boxes»];
                   Var «boxes»;Var «radii»;
                   Uop Snd (Var «source»)])
                (Var «stack»))
              (Var «certificates»)))
          (If (Binop Eq (Uop Fst (Var «source»)) (Num 1))
            (App «candle_cv_q_packed_source_certificate_sqrt_step»
              [Var «boxes»;Var «certificates»;Var «stack»])
            (App «candle_cv_q_packed_source_certificate_failure»
              [Var «stack»;Var «certificates»])))
        (If (Binop Eq (Var «source») (Num 2))
          (If (Uop Ispair (Var «stack»))
            (Pair (Num 1)
              (Pair
                (Pair
                  (App «candle_cv_q_dim_taylor_model_result_neg»
                    [Var «radii»;Uop Fst (Var «stack»)])
                  (Uop Snd (Var «stack»)))
                (Var «certificates»)))
            (App «candle_cv_q_packed_source_certificate_failure»
              [Var «stack»;Var «certificates»]))
          (If (Binop Eq (Var «source») (Num 3))
            (If (Uop Ispair (Var «stack»))
              (If (Uop Ispair (Uop Snd (Var «stack»)))
                (Pair (Num 1)
                  (Pair
                    (Pair
                      (App «candle_cv_q_dim_taylor_model_result_add»
                        [Var «radii»;
                         Uop Fst (Uop Snd (Var «stack»));
                         Uop Fst (Var «stack»)])
                      (Uop Snd (Uop Snd (Var «stack»))))
                    (Var «certificates»)))
                (App «candle_cv_q_packed_source_certificate_failure»
                  [Var «stack»;Var «certificates»]))
              (App «candle_cv_q_packed_source_certificate_failure»
                [Var «stack»;Var «certificates»]))
            (If (Binop Eq (Var «source») (Num 4))
              (If (Uop Ispair (Var «stack»))
                (If (Uop Ispair (Uop Snd (Var «stack»)))
                  (Pair (Num 1)
                    (Pair
                      (Pair
                        (App «candle_cv_q_dim_taylor_model_result_mul»
                          [Var «radii»;
                           Uop Fst (Uop Snd (Var «stack»));
                           Uop Fst (Var «stack»)])
                        (Uop Snd (Uop Snd (Var «stack»))))
                      (Var «certificates»)))
                  (App «candle_cv_q_packed_source_certificate_failure»
                    [Var «stack»;Var «certificates»]))
                (App «candle_cv_q_packed_source_certificate_failure»
                  [Var «stack»;Var «certificates»]))
              (If (Binop Eq (Var «source») (Num 5))
                (If (Uop Ispair (Var «stack»))
                  (Pair (Num 1)
                    (Pair
                      (Pair
                        (App «candle_cv_q_dim_taylor_model_result_square»
                          [Var «radii»;Uop Fst (Var «stack»)])
                        (Uop Snd (Var «stack»)))
                      (Var «certificates»)))
                  (App «candle_cv_q_packed_source_certificate_failure»
                    [Var «stack»;Var «certificates»]))
                (If (Binop Eq (Var «source») (Num 6))
                  (App «candle_cv_q_packed_source_certificate_inv_step»
                    [Var «boxes»;Var «certificates»;Var «stack»])
                  (If (Binop Eq (Var «source») (Num 7))
                    (App «candle_cv_q_packed_source_certificate_atn_step»
                      [Var «boxes»;Var «certificates»;Var «stack»])
                    (If (Binop Eq (Var «source») (Num 8))
                      (Pair (Num 1)
                        (Pair
                          (Pair
                            (App
                              «candle_cv_q_dim_taylor_model_result_pi_half»
                              [Var «radii»;
                               App «candle_cv_q_center_environment_list»
                                 [Var «boxes»];
                               Var «boxes»])
                            (Var «stack»))
                          (Var «certificates»)))
                      (App «candle_cv_q_packed_source_certificate_failure»
                        [Var «stack»;Var «certificates»])))))))))
End

Theorem bounded_packed_source_ordinary_step_lookup:
  ALOOKUP bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      «candle_cv_q_packed_source_certificate_ordinary_step» =
    SOME
      ([«boxes»;«source»;«certificates»;«stack»],
       bounded_packed_source_ordinary_step_body)
Proof
  EVAL_TAC
QED

Theorem bounded_packed_source_ordinary_step_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv source;from_cv certificates;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (subst
        [(«boxes»,from_cv boxes);(«source»,from_cv source);
         («certificates»,from_cv certificates);
         («stack»,from_cv stack)]
        bounded_packed_source_ordinary_step_body) refs
Proof
  strip_tac
  >> irule bounded_packed_compute_eval_literal_app4
  >> simp [bounded_packed_source_ordinary_step_lookup]
QED

Theorem bounded_packed_source_compute_eval_if_ispair_num:
  compute_eval clock ceqs
      (If (Uop Ispair (Num numeral)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs no_branch refs
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

Theorem bounded_packed_source_compute_eval_if_ispair_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (from_cv left) (from_cv right)))
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

Theorem bounded_packed_source_compute_eval_if_ispair_num_pair:
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

Theorem bounded_packed_source_compute_eval_if_ispair_two_stack:
  compute_eval clock ceqs
      (If
        (Uop Ispair
          (Pair (from_cv first_value)
            (Pair (from_cv second_value) (from_cv stack_tail))))
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

Theorem bounded_packed_source_compute_eval_if_ispair_snd_two_stack:
  compute_eval clock ceqs
      (If
        (Uop Ispair
          (Uop Snd
            (Pair (from_cv first_value)
              (Pair (from_cv second_value) (from_cv stack_tail)))))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_compute_eval_if_fst_num_pair_eq:
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

Theorem bounded_packed_source_compute_eval_if_num_eq:
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

Theorem bounded_packed_source_compute_eval_pair_from_results:
  compute_eval clock ceqs left_expression (refs:hol_refs) =
      (M_success (from_cv left_value),refs) /\
  compute_eval clock ceqs right_expression refs =
      (M_success (from_cv right_value),refs) ==>
  compute_eval clock ceqs (Pair left_expression right_expression) refs =
    (M_success (from_cv (Pair left_value right_value)),refs)
Proof
  strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_compute_eval_success_state:
  compute_eval clock ceqs result_expression (refs:hol_refs) =
      (M_success (from_cv result_value),refs) /\
  compute_eval clock ceqs stack_tail_expression refs =
      (M_success (from_cv stack_tail),refs) ==>
  compute_eval clock ceqs
      (Pair (Num 1)
        (Pair (Pair result_expression stack_tail_expression)
          (from_cv certificates))) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack_tail) certificates))),refs)
Proof
  strip_tac
  >> irule bounded_packed_source_compute_eval_pair_from_results
  >> conj_tac
  >- simp
       [compute_evalTheory.compute_eval_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule bounded_packed_source_compute_eval_pair_from_results
  >> conj_tac
  >- (irule bounded_packed_source_compute_eval_pair_from_results
      >> asm_rewrite_tac [])
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_ordinary_inv_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_inv_step»
        [from_cv boxes;from_cv certificates;from_cv stack]) refs = result ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 6);
         from_cv certificates;from_cv stack]) refs = result
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_atan_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_atn_step»
        [from_cv boxes;from_cv certificates;from_cv stack]) refs = result ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 7);
         from_cv certificates;from_cv stack]) refs = result
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_sqrt_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_sqrt_step»
        [from_cv boxes;from_cv certificates;from_cv stack]) refs = result ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Pair (Num 1) source_payload);
         from_cv certificates;from_cv stack]) refs = result
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_pair,
        bounded_packed_source_compute_eval_if_ispair_num_pair,
        bounded_packed_source_compute_eval_if_fst_num_pair_eq,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_poly_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_poly_program»
        [App «candle_cv_q_center_environment_list» [from_cv boxes];
         from_cv boxes;from_cv radii;
         Uop Snd (from_cv (Pair (Num 0) program))]) refs =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Pair (Num 0) program);
         from_cv certificates;from_cv stack]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_pair,
        bounded_packed_source_compute_eval_if_ispair_num_pair,
        bounded_packed_source_compute_eval_if_fst_num_pair_eq,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> conj_tac >- fs []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Theorem bounded_packed_source_ordinary_neg_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_result_neg»
        [from_cv radii;
         Uop Fst (from_cv (Pair input stack_tail))]) refs =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 2);from_cv certificates;
         from_cv (Pair input stack_tail)]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack_tail) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_ispair_pair,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_add_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_result_add»
        [from_cv radii;
         Uop Fst
           (Uop Snd (from_cv (Pair right (Pair left stack_tail))));
         Uop Fst (from_cv (Pair right (Pair left stack_tail)))]) refs =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 3);from_cv certificates;
         from_cv (Pair right (Pair left stack_tail))]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack_tail) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_ispair_pair,
        bounded_packed_source_compute_eval_if_ispair_two_stack,
        bounded_packed_source_compute_eval_if_ispair_snd_two_stack,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_mul_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_result_mul»
        [from_cv radii;
         Uop Fst
           (Uop Snd (from_cv (Pair right (Pair left stack_tail))));
         Uop Fst (from_cv (Pair right (Pair left stack_tail)))]) refs =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 4);from_cv certificates;
         from_cv (Pair right (Pair left stack_tail))]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack_tail) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_ispair_pair,
        bounded_packed_source_compute_eval_if_ispair_two_stack,
        bounded_packed_source_compute_eval_if_ispair_snd_two_stack,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_square_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_result_square»
        [from_cv radii;
         Uop Fst (from_cv (Pair input stack_tail))]) refs =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 5);from_cv certificates;
         from_cv (Pair input stack_tail)]) refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack_tail) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_ispair_pair,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> conj_tac >- fs []
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_packed_source_ordinary_pi_half_eval:
  2 < clock /\
  compute_eval (clock - 1)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]])
      (refs:hol_refs) = (M_success (from_cv radii),refs) /\
  compute_eval (clock - 2)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_dim_taylor_model_result_pi_half»
        [from_cv radii;
         App «candle_cv_q_center_environment_list» [from_cv boxes];
         from_cv boxes]) refs =
    (M_success (from_cv result_value),refs) ==>
  compute_eval clock bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      (App «candle_cv_q_packed_source_certificate_ordinary_step»
        [from_cv boxes;from_cv (Num 8);from_cv certificates;from_cv stack])
      refs =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Pair result_value stack) certificates))),refs)
Proof
  strip_tac
  >> rw [bounded_packed_source_ordinary_step_unfold]
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        bounded_packed_source_ordinary_step_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_packed_source_compute_eval_if_ispair_num,
        bounded_packed_source_compute_eval_if_num_eq,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_compute_eval_success_state)
  >> conj_tac >- fs []
  >> simp [compute_execProofTheory.compute_eval_from_cv]
QED

Definition bounded_packed_source_expression_eval_above_def:
  bounded_packed_source_expression_eval_above eval_floor expression result <=>
    !clock refs.
      eval_floor < clock ==>
      compute_eval clock
        bounded_case16594_packed_source_cell0_entry_v2173_ceqs
        expression (refs:hol_refs) = (M_success (from_cv result),refs)
End

Theorem bounded_packed_source_expression_eval_above_weaken:
  bounded_packed_source_expression_eval_above lower expression result /\
  lower <= upper ==>
  bounded_packed_source_expression_eval_above upper expression result
Proof
  rw [bounded_packed_source_expression_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_expression_eval_above_sub:
  bounded_packed_source_expression_eval_above eval_floor expression result /\
  eval_floor + shift < clock ==>
  compute_eval (clock - shift)
      bounded_case16594_packed_source_cell0_entry_v2173_ceqs
      expression (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rw [bounded_packed_source_expression_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_inv_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_source_certificate_inv_step»
        [from_cv boxes;from_cv certificates;from_cv stack])
      (Pair (Num 1) (Pair next_stack next_certificates)) ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 6) certificates stack next_stack next_certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`result` |->
              `(M_success
                 (from_cv
                   (Pair (Num 1) (Pair next_stack next_certificates))),
                refs)`]
           bounded_packed_source_ordinary_inv_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (qexists_tac `radii`
      >> qpat_x_assum
           `bounded_packed_source_expression_eval_above numeric_floor
              (App «candle_cv_q_fixed_list_round_upper» _) radii`
           (fn th =>
             mp_tac
               (REWRITE_RULE
                 [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_packed_source_certificate_inv_step» _) _`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_poly_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_dim_taylor_model_poly_program»
        [App «candle_cv_q_center_environment_list» [from_cv boxes];
         from_cv boxes;from_cv radii;
         Uop Snd (Pair (Num 0) (from_cv program))]) result_value ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Pair (Num 0) program) certificates stack
      (Pair result_value stack) certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_ordinary_poly_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `radii`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_dim_taylor_model_poly_program» _) result_value`
       (fn th =>
         mp_tac
           (REWRITE_RULE
             [bounded_packed_source_expression_eval_above_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_atan_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_source_certificate_atn_step»
        [from_cv boxes;from_cv certificates;from_cv stack])
      (Pair (Num 1) (Pair next_stack next_certificates)) ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 7) certificates stack next_stack next_certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`result` |->
              `(M_success
                 (from_cv
                   (Pair (Num 1) (Pair next_stack next_certificates))),
                refs)`]
           bounded_packed_source_ordinary_atan_eval))
  >> (conj_tac >- intLib.ARITH_TAC)
  >> conj_tac
  >- (qexists_tac `radii`
      >> qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_packed_source_certificate_atn_step» _) _`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_sqrt_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_source_certificate_sqrt_step»
        [from_cv boxes;from_cv certificates;from_cv stack])
      (Pair (Num 1) (Pair next_stack next_certificates)) ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Pair (Num 1) source_payload) certificates stack
      next_stack next_certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`result` |->
              `(M_success
                 (from_cv
                   (Pair (Num 1) (Pair next_stack next_certificates))),
                refs)`]
           bounded_packed_source_ordinary_sqrt_eval))
  >> (conj_tac >- intLib.ARITH_TAC)
  >> conj_tac
  >- (qexists_tac `radii`
      >> qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_packed_source_certificate_sqrt_step» _) _`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_neg_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_dim_taylor_model_result_neg»
        [from_cv radii;Uop Fst (from_cv (Pair input stack_tail))])
      result_value ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 2) certificates (Pair input stack_tail)
      (Pair result_value stack_tail) certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_ordinary_neg_eval)
  >> (conj_tac >- intLib.ARITH_TAC)
  >> qexists_tac `radii`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_dim_taylor_model_result_neg» _) result_value`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_add_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_dim_taylor_model_result_add»
        [from_cv radii;
         Uop Fst
           (Uop Snd (from_cv (Pair right (Pair left stack_tail))));
         Uop Fst (from_cv (Pair right (Pair left stack_tail)))])
      result_value ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 3) certificates (Pair right (Pair left stack_tail))
      (Pair result_value stack_tail) certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_ordinary_add_eval)
  >> (conj_tac >- intLib.ARITH_TAC)
  >> qexists_tac `radii`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_dim_taylor_model_result_add» _) result_value`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_mul_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_dim_taylor_model_result_mul»
        [from_cv radii;
         Uop Fst
           (Uop Snd (from_cv (Pair right (Pair left stack_tail))));
         Uop Fst (from_cv (Pair right (Pair left stack_tail)))])
      result_value ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 4) certificates (Pair right (Pair left stack_tail))
      (Pair result_value stack_tail) certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_ordinary_mul_eval)
  >> (conj_tac >- intLib.ARITH_TAC)
  >> qexists_tac `radii`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_dim_taylor_model_result_mul» _) result_value`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_square_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_dim_taylor_model_result_square»
        [from_cv radii;Uop Fst (from_cv (Pair input stack_tail))])
      result_value ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 5) certificates (Pair input stack_tail)
      (Pair result_value stack_tail) certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_ordinary_square_eval)
  >> (conj_tac >- intLib.ARITH_TAC)
  >> qexists_tac `radii`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_dim_taylor_model_result_square» _) result_value`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_ordinary_pi_half_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_dim_taylor_model_result_pi_half»
        [from_cv radii;
         App «candle_cv_q_center_environment_list» [from_cv boxes];
         from_cv boxes]) result_value ==>
  bounded_packed_source_ordinary_step_eval_above (numeric_floor + 2)
      boxes (Num 8) certificates stack
      (Pair result_value stack) certificates
Proof
  strip_tac
  >> simp [bounded_packed_source_ordinary_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_packed_source_ordinary_pi_half_eval)
  >> (conj_tac >- intLib.ARITH_TAC)
  >> qexists_tac `radii`
  >> conj_tac
  >- (qpat_x_assum
        `bounded_packed_source_expression_eval_above numeric_floor
           (App «candle_cv_q_fixed_list_round_upper» _) radii`
        (fn th =>
          mp_tac
            (REWRITE_RULE
              [bounded_packed_source_expression_eval_above_def] th))
      >> disch_then match_mp_tac
      >> intLib.ARITH_TAC)
  >> qpat_x_assum
       `bounded_packed_source_expression_eval_above numeric_floor
          (App «candle_cv_q_dim_taylor_model_result_pi_half» _) result_value`
       (fn th =>
         mp_tac
           (SIMP_RULE std_ss
             [bounded_packed_source_expression_eval_above_def,
              compute_execTheory.from_cv_def] th))
  >> disch_then match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_packed_source_dispatch_inv_eval_above:
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) radii /\
  bounded_packed_source_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_source_certificate_inv_step»
        [from_cv boxes;from_cv certificates;from_cv stack])
      (Pair (Num 1) (Pair next_stack next_certificates)) ==>
  bounded_packed_source_dispatch_step_eval_above (numeric_floor + 3)
      boxes (Num 0) (Num 6) certificates stack
      next_stack next_certificates
Proof
  strip_tac
  >> irule
       (SIMP_RULE arith_ss []
         (Q.INST [`step_floor` |-> `numeric_floor + 2`]
           bounded_packed_source_dispatch_zero_eval_above))
  >> irule bounded_packed_source_ordinary_inv_eval_above
  >> asm_rewrite_tac []
  >> qexists_tac `radii`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
