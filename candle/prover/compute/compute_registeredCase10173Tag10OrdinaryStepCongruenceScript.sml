(*****************************************************************************
 * Ordinary-step congruence across the historical tag-9 and corrected
 * tag-10 environments.  The corrected registered step adds one public
 * opcode-9 case; on every non-9 instruction used by the literal source
 * prefix/suffix, the old and corrected step bodies have the same effect.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10OrdinaryStepCongruence
Ancestors
  compute_evalRestrictedCongruence
  compute_registeredCase10173Tag10OrdinaryReachable
  compute_registeredCase10173OrdinaryStepEval
  compute_registeredCase10173Tag10UnchangedEval
  compute_registeredCase10173HistoricalChunk16Tag10Data
Libs
  bossLib preamble

Definition registered_case10173_tag10_fso_program_step_body_def:
  registered_case10173_tag10_fso_program_step_body =
    If (Uop Ispair (Var «center_instruction»))
      (If (Uop Ispair (Var «box_instruction»))
        (If (Binop Eq (Uop Fst (Var «center_instruction»)) (Num 0))
          (If (Binop Eq (Uop Fst (Var «box_instruction»)) (Num 0))
            (Pair
              (App «candle_cv_fsa_item_fixed»
                [App «candle_cv_fs_poly_program»
                  [Var «center_boxes»;Var «radii»;
                   Uop Snd (Var «center_instruction»)]])
              (Var «stack»))
            (Pair
              (App «candle_cv_fsa_item_default»
                [Var «center_boxes»;Var «boxes»])
              (Var «stack»)))
          (If (Binop Eq (Uop Fst (Var «center_instruction»)) (Num 1))
            (If (Binop Eq (Uop Fst (Var «box_instruction»)) (Num 1))
              (Pair
                (App «candle_cv_fsn_item_sqrt»
                  [Var «radii»;Uop Snd (Var «center_instruction»);
                   Uop Snd (Var «box_instruction»);
                   App «candle_cv_fsa_item_head»
                     [Var «center_boxes»;Var «boxes»;Var «stack»]])
                (App «candle_cv_fsa_item_tail» [Var «stack»]))
              (Pair
                (App «candle_cv_fsa_item_default»
                  [Var «center_boxes»;Var «boxes»])
                (Var «stack»)))
            (Pair
              (App «candle_cv_fsa_item_default»
                [Var «center_boxes»;Var «boxes»])
              (Var «stack»))))
        (Pair
          (App «candle_cv_fsa_item_default»
            [Var «center_boxes»;Var «boxes»])
          (Var «stack»)))
      (If (Uop Ispair (Var «box_instruction»))
        (Pair
          (App «candle_cv_fsa_item_default»
            [Var «center_boxes»;Var «boxes»])
          (Var «stack»))
        (If (Binop Eq (Var «center_instruction»)
              (Var «box_instruction»))
          (If (Binop Eq (Var «center_instruction») (Num 2))
            (Pair
              (App «candle_cv_fsa_item_neg»
                [Num 1;Var «radii»;
                 App «candle_cv_fsa_item_head»
                   [Var «center_boxes»;Var «boxes»;Var «stack»]])
              (App «candle_cv_fsa_item_tail» [Var «stack»]))
            (If (Binop Eq (Var «center_instruction») (Num 3))
              (Pair
                (App «candle_cv_fsa_item_add»
                  [Num 1;Var «radii»;
                   App «candle_cv_fsa_item_head»
                     [Var «center_boxes»;Var «boxes»;
                      App «candle_cv_fsa_item_tail» [Var «stack»]];
                   App «candle_cv_fsa_item_head»
                     [Var «center_boxes»;Var «boxes»;Var «stack»]])
                (App «candle_cv_fsa_item_tail»
                  [App «candle_cv_fsa_item_tail» [Var «stack»]]))
              (If (Binop Eq (Var «center_instruction») (Num 4))
                (Pair
                  (App «candle_cv_fso_item_mul»
                    [Var «radii»;
                     App «candle_cv_fsa_item_head»
                       [Var «center_boxes»;Var «boxes»;
                        App «candle_cv_fsa_item_tail» [Var «stack»]];
                     App «candle_cv_fsa_item_head»
                       [Var «center_boxes»;Var «boxes»;Var «stack»]])
                  (App «candle_cv_fsa_item_tail»
                    [App «candle_cv_fsa_item_tail» [Var «stack»]]))
                (If (Binop Eq (Var «center_instruction») (Num 5))
                  (Pair
                    (App «candle_cv_fso_item_square»
                      [Var «radii»;
                       App «candle_cv_fsa_item_head»
                         [Var «center_boxes»;Var «boxes»;Var «stack»]])
                    (App «candle_cv_fsa_item_tail» [Var «stack»]))
                  (If (Binop Eq (Var «center_instruction») (Num 6))
                    (Pair
                      (App «candle_cv_fsn_item_inv»
                        [Var «radii»;
                         App «candle_cv_fsa_item_head»
                           [Var «center_boxes»;Var «boxes»;Var «stack»]])
                      (App «candle_cv_fsa_item_tail» [Var «stack»]))
                    (If (Binop Eq (Var «center_instruction») (Num 7))
                      (Pair
                        (App «candle_cv_fsn_item_atn»
                          [Var «radii»;
                           App «candle_cv_fsa_item_head»
                             [Var «center_boxes»;Var «boxes»;Var «stack»]])
                        (App «candle_cv_fsa_item_tail» [Var «stack»]))
                      (If (Binop Eq (Var «center_instruction») (Num 8))
                        (Pair
                          (App «candle_cv_fsn_item_pi_half»
                            [Var «radii»;Var «boxes»])
                          (Var «stack»))
                        (If (Binop Eq (Var «center_instruction») (Num 9))
                          (Pair
                            (App «candle_cv_fsa_item_default»
                              [Var «center_boxes»;Var «boxes»])
                            (App «candle_cv_fsa_item_tail» [Var «stack»]))
                          (Pair
                            (App «candle_cv_fsa_item_default»
                              [Var «center_boxes»;Var «boxes»])
                            (Var «stack»))))))))))
          (Pair
            (App «candle_cv_fsa_item_default»
              [Var «center_boxes»;Var «boxes»])
            (Var «stack»))))
End



Theorem registered_case10173_tag10_fso_program_step_lookup:
  ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_fso_program_step_fixed_nonlinear» =
    SOME
      ([«center_boxes»;«boxes»;«radii»;«center_instruction»;
        «box_instruction»;«stack»],
       registered_case10173_tag10_fso_program_step_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_fso_program_step_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;
         from_cv stack]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);
         («center_instruction»,from_cv center_instruction);
         («box_instruction»,from_cv box_instruction);
         («stack»,from_cv stack)]
        registered_case10173_tag10_fso_program_step_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_compute_eval_literal_app6
  >> simp [registered_case10173_tag10_fso_program_step_lookup]
QED

Theorem registered_case10173_tag10_compute_eval_if_pair_first_zero:
  compute_eval clock ceqs
      (If (Binop Eq (Uop Fst (Pair (Num 0) (from_cv (value:cv)))) (Num 0))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  irule
    compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_if_pair0_ispair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (Num 0) (from_cv (value:cv))))
        yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_snd_pair0:
  compute_eval clock ceqs
      (Uop Snd (Pair (Num 0) (from_cv (value:cv))))
      (refs:hol_refs) =
    (M_success (from_cv value),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_exp_uses_only_from_cv:
  compute_exp_uses_only allowed (from_cv value)
Proof
  metis_tac
    [compute_evalRestrictedCongruenceTheory.cexp_value_compute_exp_uses_only,
     compute_execProofTheory.cexp_value_from_cv]
QED

Theorem registered_case10173_tag10_ordinary_eval_from_old:
  compute_exp_uses_only registered_case10173_tag10_ordinary_reachable
      expression /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      expression (refs:hol_refs) = outcome ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      expression refs = outcome
Proof
  strip_tac
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        expression refs =
      compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        expression refs` by
       (irule registered_case10173_tag10_ordinary_eval_cong
        >> asm_rewrite_tac [])
  >> fs []
QED

Theorem registered_case10173_tag10_compute_eval_if_num_not_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (Num value)) pair_branch number_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs number_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_if_num_eq:
  compute_eval clock ceqs
      (If (Binop Eq (Num left) (Num right)) yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs
      (if left = right then yes_branch else no_branch) refs
Proof
  Cases_on `left = right`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_if_pair_num_ispair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (Num tag) (from_cv (value:cv))))
        pair_branch number_branch) (refs:hol_refs) =
    compute_eval clock ceqs pair_branch refs
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_if_pair_first_num_eq:
  compute_eval clock ceqs
      (If
        (Binop Eq (Uop Fst (Pair (Num tag) (from_cv (value:cv))))
          (Num expected)) yes_branch no_branch) (refs:hol_refs) =
    compute_eval clock ceqs
      (if tag = expected then yes_branch else no_branch) refs
Proof
  Cases_on `tag = expected`
  >> simp
       [compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_fst_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_compute_eval_snd_pair_num:
  compute_eval clock ceqs
      (Uop Snd (Pair (Num tag) (from_cv (value:cv))))
      (refs:hol_refs) =
    (M_success (from_cv value),refs)
Proof
  simp
    [compute_evalTheory.compute_eval_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED


Theorem registered_case10173_tag10_fso_program_step_poly_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 0) (center_program:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 0) (box_program:cv) : cv));
       («stack»,from_cv stack)]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fsa_item_fixed»
        [App «candle_cv_fs_poly_program»
          [from_cv center_boxes;from_cv radii;
           Uop Snd (Pair (Num 0) (from_cv center_program))]])
      (from_cv stack)) refs
Proof
  simp
    [registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def]
  >> PURE_REWRITE_TAC
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_execTheory.from_cv_def,
        registered_case10173_tag10_compute_eval_if_pair0_ispair,
        registered_case10173_tag10_compute_eval_if_pair_first_zero]
  >> REFL_TAC
QED

Theorem registered_case10173_tag10_fsa_item_fixed_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsa_item_fixed» [from_cv result])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  strip_tac
  >> irule registered_case10173_tag10_ordinary_eval_from_old
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fsa_item_fixed_eval
      >> asm_rewrite_tac [])
  >> simp
        [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
         compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
         registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fso_program_step_poly_eval_from_result:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv center_program])
      (refs:hol_refs) = (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Pair (Num 0) (center_program:cv) : cv);
         from_cv (Pair (Num 0) (box_program:cv) : cv);
         from_cv stack]) refs =
    (M_success
      (from_cv (Pair (Pair (Num 1) (result:cv) : cv) (stack:cv) : cv)),
     refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,
              from_cv (Pair (Num 0) (center_program:cv) : cv));
             («box_instruction»,
              from_cv (Pair (Num 0) (box_program:cv) : cv));
             («stack»,from_cv stack)]
            registered_case10173_tag10_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_tag10_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_tag10_fso_program_step_poly_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_tag10_ceqs
              (App «candle_cv_fsa_item_fixed» [from_cv result]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> irule EQ_TRANS
          >> qexists_tac
               `compute_eval (clock - 1)
                  registered_case10173_historical_chunk16_tag10_ceqs
                  (App «candle_cv_fs_poly_program»
                    [from_cv center_boxes;from_cv radii;
                     from_cv center_program]) refs`
          >> conj_tac
          >- (irule
                compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
              >> conj_tac >- intLib.ARITH_TAC
              >> conj_tac
              >- irule compute_execProofTheory.compute_eval_from_cv
              >> conj_tac
              >- irule compute_execProofTheory.compute_eval_from_cv
              >> irule registered_case10173_tag10_compute_eval_snd_pair0)
          >> asm_rewrite_tac [])
      >> irule registered_case10173_tag10_fsa_item_fixed_eval
      >> intLib.ARITH_TAC)
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_tag10_fso_program_step_mul_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,from_cv (Num 4));
       («box_instruction»,from_cv (Num 4));
       («stack»,from_cv
         (Pair (right:cv) (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fso_item_mul»
        [from_cv radii;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            App «candle_cv_fsa_item_tail»
              [from_cv
                (Pair (right:cv)
                  (Pair (left:cv) (stack_tail:cv) : cv) : cv)]];
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            from_cv
              (Pair (right:cv)
                (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail»
          [from_cv
            (Pair (right:cv)
              (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])) refs
Proof
  simp
    [registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     registered_case10173_tag10_compute_eval_if_num_not_pair,
     registered_case10173_tag10_compute_eval_if_num_eq]
QED

Theorem registered_case10173_tag10_fsa_item_head_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsa_item_head»
        [from_cv center_boxes;from_cv boxes;
         from_cv (Pair (item:cv) (stack_tail:cv) : cv)])
      (refs:hol_refs) = (M_success (from_cv item),refs)
Proof
  strip_tac
  >> irule registered_case10173_tag10_ordinary_eval_from_old
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
      >> asm_rewrite_tac [])
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fsa_item_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsa_item_tail»
        [from_cv (Pair (item:cv) (stack_tail:cv) : cv)])
      (refs:hol_refs) = (M_success (from_cv stack_tail),refs)
Proof
  strip_tac
  >> irule registered_case10173_tag10_ordinary_eval_from_old
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_tail_cons_eval
      >> asm_rewrite_tac [])
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fsa_item_head_after_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsa_item_head»
        [from_cv center_boxes;from_cv boxes;
         App «candle_cv_fsa_item_tail»
           [from_cv
             (Pair (right:cv)
               (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (refs:hol_refs) = (M_success (from_cv left),refs)
Proof
  strip_tac
  >> irule registered_case10173_tag10_ordinary_eval_from_old
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fsa_item_head_after_tail_cons_eval
      >> asm_rewrite_tac [])
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fsa_item_tail_after_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail»
          [from_cv
            (Pair (right:cv)
              (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (refs:hol_refs) = (M_success (from_cv stack_tail),refs)
Proof
  strip_tac
  >> irule registered_case10173_tag10_ordinary_eval_from_old
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fsa_item_tail_after_tail_cons_eval
      >> asm_rewrite_tac [])
  >> simp
       [compute_evalRestrictedCongruenceTheory.compute_exp_uses_only_def,
        compute_registeredCase10173Tag10OrdinaryReachableTheory.registered_case10173_tag10_ordinary_reachable_def,
        registered_case10173_tag10_compute_exp_uses_only_from_cv]
QED

Theorem registered_case10173_tag10_fso_program_step_add_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,from_cv (Num 3));
       («box_instruction»,from_cv (Num 3));
       («stack»,from_cv
         (Pair (right:cv) (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fsa_item_add»
        [Num 1;from_cv radii;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            App «candle_cv_fsa_item_tail»
              [from_cv
                (Pair (right:cv)
                  (Pair (left:cv) (stack_tail:cv) : cv) : cv)]];
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            from_cv
              (Pair (right:cv)
                (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail»
          [from_cv
            (Pair (right:cv)
              (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])) refs
Proof
  simp
    [registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     registered_case10173_tag10_compute_eval_if_num_not_pair,
     registered_case10173_tag10_compute_eval_if_num_eq]
QED

Theorem registered_case10173_tag10_fso_program_step_sqrt_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 1) (center_certificate:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 1) (box_certificate:cv) : cv));
       («stack»,from_cv (Pair (input:cv) (stack_tail:cv) : cv))]
      registered_case10173_tag10_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (Pair
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;
         Uop Snd (Pair (Num 1) (from_cv center_certificate));
         Uop Snd (Pair (Num 1) (from_cv box_certificate));
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            from_cv (Pair (input:cv) (stack_tail:cv) : cv)]])
      (App «candle_cv_fsa_item_tail»
        [from_cv (Pair (input:cv) (stack_tail:cv) : cv)])) refs
Proof
  simp
    [registered_case10173_tag10_fso_program_step_body_def,
     compute_evalTheory.subst_def,
     compute_execProofTheory.subst_from_cv,
     compute_execTheory.from_cv_def,
     registered_case10173_tag10_compute_eval_if_pair_num_ispair,
     registered_case10173_tag10_compute_eval_if_pair_first_num_eq]
QED

Theorem registered_case10173_tag10_fso_program_step_mul_eval_from_item:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_item_mul»
        [from_cv radii;from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Num 4);from_cv (Num 4);
         from_cv
           (Pair (right:cv)
             (Pair (left:cv) (stack_tail:cv) : cv) : cv)]) refs =
    (M_success
      (from_cv (Pair (item:cv) (stack_tail:cv) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,from_cv (Num 4));
             («box_instruction»,from_cv (Num 4));
             («stack»,from_cv
               (Pair (right:cv)
                 (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
            registered_case10173_tag10_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_tag10_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_tag10_fso_program_step_mul_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_tag10_ceqs
              (App «candle_cv_fso_item_mul»
                [from_cv radii;from_cv left;from_cv right]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> conj_tac
          >- (irule
                registered_case10173_tag10_fsa_item_head_after_tail_cons_eval
              >> intLib.ARITH_TAC)
          >> irule registered_case10173_tag10_fsa_item_head_cons_eval
          >> intLib.ARITH_TAC)
      >> fs [])
  >> irule registered_case10173_tag10_fsa_item_tail_after_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_tag10_fso_program_step_add_eval_from_item:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsa_item_add»
        [from_cv (Num 1);from_cv radii;from_cv left;from_cv right])
      (refs:hol_refs) = (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Num 3);from_cv (Num 3);
         from_cv
           (Pair (right:cv)
             (Pair (left:cv) (stack_tail:cv) : cv) : cv)]) refs =
    (M_success
      (from_cv (Pair (item:cv) (stack_tail:cv) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,from_cv (Num 3));
             («box_instruction»,from_cv (Num 3));
             («stack»,from_cv
               (Pair (right:cv)
                 (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
            registered_case10173_tag10_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_tag10_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_tag10_fso_program_step_add_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_tag10_ceqs
              (App «candle_cv_fsa_item_add»
                [from_cv (Num 1);from_cv radii;
                 from_cv left;from_cv right]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- simp
               [Once compute_evalTheory.compute_eval_def,
                compute_execTheory.from_cv_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> conj_tac
          >- (irule
                registered_case10173_tag10_fsa_item_head_after_tail_cons_eval
              >> intLib.ARITH_TAC)
          >> irule registered_case10173_tag10_fsa_item_head_cons_eval
          >> intLib.ARITH_TAC)
      >> fs [])
  >> irule registered_case10173_tag10_fsa_item_tail_after_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_tag10_fso_program_step_sqrt_eval_from_item:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;from_cv input]) (refs:hol_refs) =
    (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv (Pair (Num 1) (center_certificate:cv) : cv);
         from_cv (Pair (Num 1) (box_certificate:cv) : cv);
         from_cv (Pair (input:cv) (stack_tail:cv) : cv)]) refs =
    (M_success
      (from_cv (Pair (item:cv) (stack_tail:cv) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_tag10_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,
              from_cv (Pair (Num 1) (center_certificate:cv) : cv));
             («box_instruction»,
              from_cv (Pair (Num 1) (box_certificate:cv) : cv));
             («stack»,from_cv
               (Pair (input:cv) (stack_tail:cv) : cv))]
            registered_case10173_tag10_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_tag10_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_tag10_fso_program_step_sqrt_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_tag10_ceqs
              (App «candle_cv_fsn_item_sqrt»
                [from_cv radii;from_cv center_certificate;
                 from_cv box_certificate;from_cv input]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> conj_tac
          >- irule registered_case10173_tag10_compute_eval_snd_pair_num
          >> conj_tac
          >- irule registered_case10173_tag10_compute_eval_snd_pair_num
          >> irule registered_case10173_tag10_fsa_item_head_cons_eval
          >> intLib.ARITH_TAC)
      >> fs [])
  >> irule registered_case10173_tag10_fsa_item_tail_cons_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
