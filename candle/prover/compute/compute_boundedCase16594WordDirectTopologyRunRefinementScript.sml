(*****************************************************************************
 * Refinement of the ordinary compact topology loop by the direct cv runner. *
 *****************************************************************************)
Theory compute_boundedCase16594WordDirectTopologyRunRefinement
Ancestors
  compute_boundedCase16594WordDirectTopologyTransitionRefinement
  compute_boundedCase16594Cell0WholeCompactRunEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_cell0_whole_compact_run_zero_eval:
  !dimension jobs stack clock refs.
    3 < clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num dimension);from_cv (Num 0);from_cv jobs;from_cv stack])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) (Pair jobs stack))),refs)
Proof
  rpt strip_tac
  >> rw
       [compute_boundedCase16594Cell0WholeCompactRunEvalTheory.bounded_case16594_cell0_whole_compact_run_unfold]
  >> simp
       [compute_boundedCase16594Cell0WholeCompactRunEvalTheory.bounded_case16594_cell0_whole_compact_run_body_def,
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

Theorem bounded_case16594_direct_topology_run_eval:
  !dimension tokens jobs stack remaining_jobs final_stack clock refs.
    bounded_case16594_direct_topology_run dimension tokens jobs stack =
      SOME (remaining_jobs,final_stack) /\
    bounded_case16594_direct_cv_list_length tokens * (dimension + 42) + 4 <
      clock ==>
    compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num dimension);from_cv tokens;from_cv jobs;from_cv stack])
      (refs:hol_refs) =
    (M_success
      (from_cv (Pair (Num 1) (Pair remaining_jobs final_stack))),refs)
Proof
  gen_tac
  >> ho_match_mp_tac (TypeBase.induction_of ``:cv``)
  >> conj_tac
  >- (rpt gen_tac
      >> simp
           [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_run_def,
            compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_cv_list_length_def]
      >> rpt strip_tac
      >> irule
           (PURE_REWRITE_RULE [compute_execTheory.from_cv_def]
             bounded_case16594_cell0_whole_compact_run_zero_eval)
      >> fs [])
  >> rpt gen_tac
  >> strip_tac
  >> rpt gen_tac
  >> Cases_on
       `bounded_case16594_direct_topology_transition dimension tokens'
          jobs stack`
  >> fs
       [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_run_def]
  >> PairCases_on `x`
  >> simp
       [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_cv_list_length_def]
  >> rpt strip_tac
  >> subgoal `0 < clock` >- intLib.ARITH_TAC
  >> rw
       [SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          (Q.INST
            [`tree_dim` |-> `Num dimension`,
             `token_stream` |-> `Pair tokens' tokens''`]
            compute_boundedCase16594Cell0WholeCompactRunEvalTheory.bounded_case16594_cell0_whole_compact_run_unfold)]
  >> simp
       [compute_boundedCase16594Cell0WholeCompactRunEvalTheory.bounded_case16594_cell0_whole_compact_run_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> rw
       [compute_boundedPackedObjectDotRecursiveEvalTheory.bounded_packed_compute_eval_if_ispair_pair]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `Pair (Num 1) (Pair x0 x1)`
  >> conj_tac
  >- (irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_cell0_whole_combined_ceqs
              (App
                «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition»
                [from_cv (Num dimension);from_cv tokens';from_cv jobs;
                 from_cv stack]) refs`
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
                ml_monadBaseTheory.st_ex_return_def])
      >> irule
           compute_boundedCase16594WordDirectTopologyTransitionRefinementTheory.bounded_case16594_direct_topology_transition_eval
      >> conj_tac
      >- (fs [arithmeticTheory.MULT] >> intLib.ARITH_TAC)
      >> asm_rewrite_tac [])
  >> simp
       [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv,
        compute_execTheory.from_cv_def]
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
            [from_cv (Num dimension);from_cv tokens'';from_cv x0;
             from_cv x1]) refs`
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
      >> fs [arithmeticTheory.MULT]
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> first_x_assum irule
  >> conj_tac
  >- (fs [arithmeticTheory.MULT] >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
