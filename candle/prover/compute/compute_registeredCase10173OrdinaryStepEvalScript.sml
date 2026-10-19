(*****************************************************************************
 * Structural evaluator semantics for one ordinary paired program step.
 *
 * The authenticated case-10173 source prefix and suffix use only paired
 * polynomial, square-root, multiplication, and addition instructions.  This
 * layer exposes the registered six-argument step once so those four stack
 * effects can be proved independently and then folded over the literal
 * 31- and 15-instruction templates.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryStepEval
Ancestors
  compute_registeredCase10173OrdinaryOperationEval
Libs
  bossLib preamble

Definition registered_case10173_fso_program_step_body_def:
  registered_case10173_fso_program_step_body =
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
                        (Pair
                          (App «candle_cv_fsa_item_default»
                            [Var «center_boxes»;Var «boxes»])
                          (Var «stack»)))))))))
          (Pair
            (App «candle_cv_fsa_item_default»
              [Var «center_boxes»;Var «boxes»])
            (Var «stack»))))
End

Theorem registered_case10173_fso_program_step_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fso_program_step_fixed_nonlinear» =
    SOME
      ([«center_boxes»;«boxes»;«radii»;«center_instruction»;
        «box_instruction»;«stack»],
       registered_case10173_fso_program_step_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_compute_eval_literal_app6:
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

Theorem registered_case10173_fso_program_step_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_program_step_fixed_nonlinear»
        [from_cv center_boxes;from_cv boxes;from_cv radii;
         from_cv center_instruction;from_cv box_instruction;
         from_cv stack]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);
         («center_instruction»,from_cv center_instruction);
         («box_instruction»,from_cv box_instruction);
         («stack»,from_cv stack)]
        registered_case10173_fso_program_step_body) refs
Proof
  strip_tac
  >> irule registered_case10173_compute_eval_literal_app6
  >> simp [registered_case10173_fso_program_step_lookup]
QED

Theorem registered_case10173_fso_program_step_mul_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,from_cv (Num 4));
       («box_instruction»,from_cv (Num 4));
       («stack»,from_cv
         (Pair (right:cv) (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
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
    [registered_case10173_fso_program_step_body_def,
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
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fsa_item_head_after_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_head»
        [from_cv center_boxes;from_cv boxes;
         App «candle_cv_fsa_item_tail»
           [from_cv
             (Pair (right:cv)
               (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (refs:hol_refs) = (M_success (from_cv left),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsa_item_head»
            [from_cv center_boxes;from_cv boxes;
             from_cv (Pair (left:cv) (stack_tail:cv) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac >- irule compute_execProofTheory.compute_eval_from_cv
      >> conj_tac >- irule compute_execProofTheory.compute_eval_from_cv
      >> irule
           compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_tail_cons_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fsa_item_tail_after_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_tail»
        [App «candle_cv_fsa_item_tail»
          [from_cv
            (Pair (right:cv)
              (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (refs:hol_refs) = (M_success (from_cv stack_tail),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fsa_item_tail»
            [from_cv (Pair (left:cv) (stack_tail:cv) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- asm_rewrite_tac []
      >> irule
           compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_tail_cons_eval
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_tail_cons_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fso_program_step_mul_eval_from_item:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fso_item_mul»
        [from_cv radii;from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
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
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,from_cv (Num 4));
             («box_instruction»,from_cv (Num 4));
             («stack»,from_cv
               (Pair (right:cv)
                 (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
            registered_case10173_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fso_program_step_mul_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fso_item_mul»
                [from_cv radii;from_cv left;from_cv right]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> conj_tac
          >- (irule registered_case10173_fsa_item_head_after_tail_cons_eval
              >> intLib.ARITH_TAC)
          >> irule
               compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
          >> intLib.ARITH_TAC)
      >> fs [])
  >> irule registered_case10173_fsa_item_tail_after_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_program_step_add_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,from_cv (Num 3));
       («box_instruction»,from_cv (Num 3));
       («stack»,from_cv
         (Pair (right:cv) (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
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
    [registered_case10173_fso_program_step_body_def,
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
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fso_program_step_add_eval_from_item:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_add»
        [from_cv (Num 1);from_cv radii;from_cv left;from_cv right])
      (refs:hol_refs) = (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
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
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,from_cv (Num 3));
             («box_instruction»,from_cv (Num 3));
             («stack»,from_cv
               (Pair (right:cv)
                 (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
            registered_case10173_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fso_program_step_add_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
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
          >- (irule registered_case10173_fsa_item_head_after_tail_cons_eval
              >> intLib.ARITH_TAC)
          >> irule
               compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
          >> intLib.ARITH_TAC)
      >> fs [])
  >> irule registered_case10173_fsa_item_tail_after_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_program_step_sqrt_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 1) (center_certificate:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 1) (box_certificate:cv) : cv));
       («stack»,from_cv (Pair (input:cv) (stack_tail:cv) : cv))]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (Pair
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;from_cv box_certificate;
         App «candle_cv_fsa_item_head»
           [from_cv center_boxes;from_cv boxes;
            from_cv (Pair (input:cv) (stack_tail:cv) : cv)]])
      (App «candle_cv_fsa_item_tail»
        [from_cv (Pair (input:cv) (stack_tail:cv) : cv)])) refs
Proof
  simp
    [registered_case10173_fso_program_step_body_def,
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

Theorem registered_case10173_fso_program_step_sqrt_eval_from_item:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;from_cv input]) (refs:hol_refs) =
    (M_success (from_cv item),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
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
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,
              from_cv (Pair (Num 1) (center_certificate:cv) : cv));
             («box_instruction»,
              from_cv (Pair (Num 1) (box_certificate:cv) : cv));
             («stack»,from_cv
               (Pair (input:cv) (stack_tail:cv) : cv))]
            registered_case10173_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fso_program_step_sqrt_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
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
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> irule
               compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
          >> intLib.ARITH_TAC)
      >> fs [])
  >> irule
       compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_program_step_poly_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (subst
      [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
       («radii»,from_cv radii);
       («center_instruction»,
        from_cv (Pair (Num 0) (center_program:cv) : cv));
       («box_instruction»,
        from_cv (Pair (Num 0) (box_program:cv) : cv));
       («stack»,from_cv stack)]
      registered_case10173_fso_program_step_body) (refs:hol_refs) =
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (Pair
      (App «candle_cv_fsa_item_fixed»
        [App «candle_cv_fs_poly_program»
          [from_cv center_boxes;from_cv radii;from_cv center_program]])
      (from_cv stack)) refs
Proof
  simp
    [registered_case10173_fso_program_step_body_def,
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

Theorem registered_case10173_fso_program_step_poly_eval_from_result:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv center_program])
      (refs:hol_refs) = (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
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
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
             («radii»,from_cv radii);
             («center_instruction»,
              from_cv (Pair (Num 0) (center_program:cv) : cv));
             («box_instruction»,
              from_cv (Pair (Num 0) (box_program:cv) : cv));
             («stack»,from_cv stack)]
            registered_case10173_fso_program_step_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fso_program_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC
       [registered_case10173_fso_program_step_poly_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fsa_item_fixed» [from_cv result]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> fs [])
      >> irule
           compute_registeredCase10173HistCompletionEvalTheory.registered_case10173_fsa_item_fixed_eval
      >> intLib.ARITH_TAC)
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

val _ = export_theory ();
