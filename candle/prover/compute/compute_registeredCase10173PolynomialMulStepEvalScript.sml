(*****************************************************************************
 * Registered multiplication instruction for literal polynomial programs.
 *
 * The compact typed multiplication contract is already clock-uniform.  This
 * layer proves the unchanged postfix runner's stack access and instruction
 * control once, so a successful typed product can be inserted directly into
 * a compositional polynomial trace.
 *****************************************************************************)
Theory compute_registeredCase10173PolynomialMulStepEval
Ancestors
  compute_registeredCase10173PolynomialTraceEval
  compute_registeredCase10173ResultMulAboveEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fs_result_tail_body_def:
  registered_case10173_fs_result_tail_body =
    If (Uop Ispair (Var «stack»))
      (Uop Snd (Var «stack»))
      (Num 0)
End

Theorem registered_case10173_fs_result_tail_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_result_tail» =
    SOME ([«stack»],registered_case10173_fs_result_tail_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_result_tail_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_tail» [from_cv stack]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst [(«stack»,from_cv stack)]
        registered_case10173_fs_result_tail_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_literal_app1
  >> simp [registered_case10173_fs_result_tail_lookup]
QED

Theorem registered_case10173_fs_result_tail_cons_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«stack»,from_cv (Pair (stack_head:cv) (stack_tail:cv) : cv))]
        registered_case10173_fs_result_tail_body) (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (from_cv stack_tail) refs
Proof
  simp
    [registered_case10173_fs_result_tail_body_def,
     Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.subst_def,
     compute_execTheory.from_cv_def,
     compute_execProofTheory.compute_eval_from_cv,
     compute_evalTheory.do_uop_def,
     compute_evalTheory.do_ispair_def,
     compute_evalTheory.do_snd_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_result_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_tail»
        [from_cv (Pair (stack_head:cv) (stack_tail:cv) : cv)])
      (refs:hol_refs) = (M_success (from_cv stack_tail),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«stack»,from_cv
                (Pair (stack_head:cv) (stack_tail:cv) : cv))]
            registered_case10173_fs_result_tail_body) refs`
  >> conj_tac
  >- (irule registered_case10173_fs_result_tail_unfold
      >> asm_rewrite_tac [])
  >> PURE_REWRITE_TAC [registered_case10173_fs_result_tail_cons_control_eval]
  >> irule compute_execProofTheory.compute_eval_from_cv
QED

Theorem registered_case10173_fs_result_head_after_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_head»
        [from_cv dimensions;
         App «candle_cv_fs_result_tail»
           [from_cv
             (Pair (right:cv)
               (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (refs:hol_refs) = (M_success (from_cv left),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_head»
            [from_cv dimensions;
             from_cv (Pair (left:cv) (stack_tail:cv) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> simp [compute_execProofTheory.compute_eval_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`stack_head:cv` |-> `right`,
                `stack_tail:cv` |-> `Pair left stack_tail`]
               registered_case10173_fs_result_tail_cons_eval))
      >> asm_rewrite_tac [])
  >> irule
       compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_result_head_cons_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_result_tail_after_tail_cons_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_tail»
        [App «candle_cv_fs_result_tail»
          [from_cv
            (Pair (right:cv)
              (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
      (refs:hol_refs) = (M_success (from_cv stack_tail),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_result_tail»
            [from_cv (Pair (left:cv) (stack_tail:cv) : cv)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- asm_rewrite_tac []
      >> irule
           (Q.INST
             [`stack_head:cv` |-> `right`,
              `stack_tail:cv` |-> `Pair left stack_tail`]
             registered_case10173_fs_result_tail_cons_eval)
      >> asm_rewrite_tac [])
  >> irule registered_case10173_fs_result_tail_cons_eval
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_fs_poly_step_mul_control_eval:
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (subst
        [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
         («instruction»,from_cv (Num 4));
         («stack»,from_cv
           (Pair (right:cv)
             (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
        registered_case10173_fs_poly_step_body)
      (refs:hol_refs) =
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (Pair
        (App «candle_cv_fs_result_mul»
          [from_cv radii;
           App «candle_cv_fs_result_head»
             [from_cv dimensions;
              App «candle_cv_fs_result_tail»
                [from_cv
                  (Pair (right:cv)
                    (Pair (left:cv) (stack_tail:cv) : cv) : cv)]];
           App «candle_cv_fs_result_head»
             [from_cv dimensions;
              from_cv
                (Pair (right:cv)
                  (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])
        (App «candle_cv_fs_result_tail»
          [App «candle_cv_fs_result_tail»
            [from_cv
              (Pair (right:cv)
                (Pair (left:cv) (stack_tail:cv) : cv) : cv)]])) refs
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
     compute_evalTheory.do_binop_def,
     compute_evalTheory.do_eq_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_ignore_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_poly_step_mul_eval_from_result:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_result_mul»
        [from_cv radii;from_cv left;from_cv right]) (refs:hol_refs) =
    (M_success (from_cv result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_poly_step»
        [from_cv dimensions;from_cv radii;from_cv (Num 4);
         from_cv
           (Pair (right:cv)
             (Pair (left:cv) (stack_tail:cv) : cv) : cv)]) refs =
    (M_success
      (from_cv (Pair (result:cv) (stack_tail:cv) : cv)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (subst
            [(«dimensions»,from_cv dimensions);(«radii»,from_cv radii);
             («instruction»,from_cv (Num 4));
             («stack»,from_cv
               (Pair (right:cv)
                 (Pair (left:cv) (stack_tail:cv) : cv) : cv))]
            registered_case10173_fs_poly_step_body) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_poly_step_unfold
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [registered_case10173_fs_poly_step_mul_control_eval]
  >> irule
       compute_registeredCase10173CanonicalEvalTheory.compute_eval_pair_from_results
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_result_mul»
                [from_cv radii;from_cv left;from_cv right]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app3_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac
          >- irule compute_execProofTheory.compute_eval_from_cv
          >> conj_tac
          >- (irule registered_case10173_fs_result_head_after_tail_cons_eval
              >> intLib.ARITH_TAC)
          >> irule
               compute_registeredCase10173ActualVariableProgramEvalTheory.registered_case10173_fs_result_head_cons_eval
          >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> irule registered_case10173_fs_result_tail_after_tail_cons_eval
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_poly_mul_step_eval_above:
  registered_case10173_eval_above result_floor
      (App «candle_cv_fs_result_mul»
        [from_cv radii;from_cv left;from_cv right]) result ==>
  registered_case10173_poly_step_eval_above (result_floor + 2)
      dimensions radii (Num 4)
      (Pair right (Pair left stack_tail))
      (Pair result stack_tail)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173PolynomialTraceEvalTheory.registered_case10173_poly_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_poly_step_mul_eval_from_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> fs
       [compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
