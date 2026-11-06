(*****************************************************************************
 * Generic recursive whole-jobs wrapper lemmas for fixed-word production.    *
 *                                                                           *
 * These lemmas isolate the unchanged Candle list wrapper from the numerical  *
 * callback.  A successful head job and successful tail at the wrapper's      *
 * recursive clock imply success of the corresponding cons cell.              *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeJobsProducer
Ancestors
  compute_boundedCase16594WordWholeJobProducer
  compute_boundedCase16594Cell0WholeJobsEval
Libs
  bossLib preamble intLib

Theorem bounded_case16594_word_whole_jobs_empty_eval:
  3 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv plan_codes;from_cv source_instructions;
       from_cv (Num 0);from_cv (Num 0)]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_jobs_check_unfold]
  >> simp
       [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_jobs_check_body_def,
        compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_named_lookup,
        compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_body_def,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        compute_evalTheory.compute_eval_def,compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_eq_def,compute_evalTheory.do_binop_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem bounded_case16594_word_whole_jobs_cons_eval:
  1 < clock /\
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv plan_codes;from_cv source_instructions;
       from_cv packed_cell;from_cv job]) (refs:hol_refs) =
      (M_success (Num 1),refs) /\
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv plan_codes;from_cv source_instructions;
       from_cv packed_cells;from_cv jobs]) refs =
      (M_success (Num 1),refs)
  ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv plan_codes;from_cv source_instructions;
       from_cv (Pair packed_cell packed_cells);
       from_cv (Pair job jobs)]) refs =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_jobs_check_unfold]
  >> simp
       [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_jobs_check_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_if_true_result
  >> conj_tac
  >- simp
       [compute_execProofTheory.compute_eval_from_cv,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_bool_and_true_one_eval
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (irule
        compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_eq_one
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval (clock - 1)
              bounded_case16594_cell0_whole_combined_ceqs
              (App «candle_cv_q_packed_object_whole_job_check»
                [from_cv plan_codes;from_cv source_instructions;
                 from_cv packed_cell;from_cv job]) refs`
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
      >> asm_rewrite_tac [compute_execTheory.from_cv_def])
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          bounded_case16594_cell0_whole_combined_ceqs
          (App «candle_cv_q_packed_object_whole_jobs_check»
            [from_cv plan_codes;from_cv source_instructions;
             from_cv packed_cells;from_cv jobs]) refs`
  >> conj_tac
  >- (irule
        compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_app4_argument_results
      >> simp
           [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_compute_eval_pair_snd,
            compute_execProofTheory.compute_eval_from_cv,
            compute_execTheory.from_cv_def,
            compute_evalTheory.compute_eval_def,
            compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
            ml_monadBaseTheory.st_ex_bind_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
