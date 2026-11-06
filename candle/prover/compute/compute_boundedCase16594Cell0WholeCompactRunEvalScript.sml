(*****************************************************************************
 * The one-token compact topology recursion for genuine case16594 cell 0.    *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeCompactRunEval
Ancestors
  compute_boundedCase16594Cell0WholeTopologyEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_cell0_whole_compact_run_body_def:
  bounded_case16594_cell0_whole_compact_run_body =
    If (Uop Ispair (Var «tokens»))
      (Let «transition»
        (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»
          [Var «tree_dim»;Uop Fst (Var «tokens»);
           Var «jobs»;Var «stack»])
        (If (Uop Fst (Var «transition»))
          (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
            [Var «tree_dim»;Uop Snd (Var «tokens»);
             Uop Fst (Uop Snd (Var «transition»));
             Uop Snd (Uop Snd (Var «transition»))])
          (Pair (Num 0) (Pair (Var «jobs») (Var «stack»)))))
      (If (Binop Eq (Var «tokens») (Num 0))
        (Pair (Num 1) (Pair (Var «jobs») (Var «stack»)))
        (Pair (Num 0) (Pair (Var «jobs») (Var «stack»))))
End

Theorem bounded_case16594_cell0_whole_compact_run_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run» =
    SOME
      ([«tree_dim»;«tokens»;«jobs»;«stack»],
       bounded_case16594_cell0_whole_compact_run_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_compact_run_lookup,
     bounded_case16594_cell0_whole_compact_run_body_def]
QED

Theorem bounded_case16594_cell0_whole_compact_run_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
      [from_cv tree_dim;from_cv token_stream;from_cv jobs;from_cv stack])
    (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
    (subst
      [(«tree_dim»,from_cv tree_dim);(«tokens»,from_cv token_stream);
       («jobs»,from_cv jobs);(«stack»,from_cv stack)]
      bounded_case16594_cell0_whole_compact_run_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_compute_eval_literal_app4
  >> simp [bounded_case16594_cell0_whole_compact_run_named_lookup]
QED

Theorem bounded_case16594_cell0_whole_compute_eval_if_ispair_num_pair:
  compute_eval clock ceqs
      (If (Uop Ispair (Pair (Num left) (Num right)))
        yes_branch no_branch)
      (refs:hol_refs) =
    compute_eval clock ceqs yes_branch refs
Proof
  simp
    [Once compute_evalTheory.compute_eval_def,
     compute_evalTheory.compute_eval_def,
     compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
     ml_monadBaseTheory.st_ex_bind_def,
     ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_compact_run_empty_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
      [from_cv bounded_case16594_cell0_whole_tree_dim;
       from_cv (Num 0);from_cv (Num 0);
       from_cv
         (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))])
    (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_compact_run_unfold]
  >> simp
       [bounded_case16594_cell0_whole_compact_run_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> rw
       [compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_num]
  >> simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,compute_evalTheory.do_eq_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_cell0_whole_compact_run_singleton_eval:
  20 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
      [from_cv bounded_case16594_cell0_whole_tree_dim;
       from_cv bounded_case16594_cell0_whole_tokens;
       from_cv bounded_case16594_cell0_whole_encoded_jobs;
       from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))))),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_compact_run_unfold]
  >> simp
       [bounded_case16594_cell0_whole_compact_run_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv,
        compute_boundedCase16594Cell0WholePayloadsTheory.bounded_case16594_cell0_whole_tokens_def,
        bounded_case16594_cell0_whole_compute_eval_if_ispair_num_pair]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair (Num 1)
          (Pair (Num 0)
            (Pair bounded_case16594_cell0_whole_job_metadata (Num 0)))`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_cell0_whole_combined_ceqs
              (App
                «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»
                [from_cv bounded_case16594_cell0_whole_tree_dim;
                 from_cv (Num 0);
                 from_cv bounded_case16594_cell0_whole_encoded_jobs;
                 from_cv (Num 0)]) refs`
      >> conj_tac
      >- (irule
            compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_app4_argument_results
          >> simp
               [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_pair_fst,
                compute_execProofTheory.compute_eval_from_cv,
                compute_execTheory.from_cv_def,
                compute_evalTheory.compute_eval_def,
                compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
                ml_monadBaseTheory.st_ex_bind_def,
                ml_monadBaseTheory.st_ex_return_def]
          >> intLib.ARITH_TAC)
      >> irule
           compute_boundedCase16594Cell0WholeTopologyEvalTheory.bounded_case16594_cell0_whole_leaf_transition_eval
      >> intLib.ARITH_TAC)
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 2)
          bounded_case16594_cell0_whole_combined_ceqs
          (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
            [from_cv bounded_case16594_cell0_whole_tree_dim;
             from_cv (Num 0);from_cv (Num 0);
             from_cv
               (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_app4_argument_results
      >> simp
           [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_pair_fst,
            compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_pair_snd,
            compute_execProofTheory.compute_eval_from_cv,
            compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
            compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         bounded_case16594_cell0_whole_compact_run_empty_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
