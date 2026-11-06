(*****************************************************************************
 * Root evaluator theorem for the genuine case16594 cell-0 whole call.       *
 *****************************************************************************)
Theory compute_boundedCase16594Cell0WholeEval
Ancestors
  compute_boundedCase16594Cell0WholeCompactRunEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_cell0_whole_check_body_def:
  bounded_case16594_cell0_whole_check_body =
    Let «plan_codes» (Uop Fst (Var «source_descriptor»))
      (Let «source_and_cells» (Uop Snd (Var «source_descriptor»))
        (Let «source_instructions» (Uop Fst (Var «source_and_cells»))
          (Let «packed_cells» (Uop Snd (Var «source_and_cells»))
            (Pair
              (App «candle_cv_q_packed_object_whole_jobs_check»
                [Var «plan_codes»;Var «source_instructions»;
                 Var «packed_cells»;Var «encoded_jobs»])
              (App
                «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
                [Var «tree_dim»;Var «tokens»;Var «encoded_jobs»;
                 Num 0])))))
End

Theorem bounded_case16594_cell0_whole_check_named_lookup:
  ALOOKUP bounded_case16594_cell0_whole_combined_ceqs
      «candle_cv_q_packed_object_whole_check» =
    SOME
      ([«source_descriptor»;«tree_dim»;«tokens»;«encoded_jobs»],
       bounded_case16594_cell0_whole_check_body)
Proof
  rw
    [compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_whole_check_lookup,
     bounded_case16594_cell0_whole_check_body_def]
QED

Theorem bounded_case16594_cell0_whole_check_unfold:
  0 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_check»
      [from_cv source_descriptor;from_cv tree_dim;
       from_cv token_stream;from_cv encoded_jobs]) (refs:hol_refs) =
  compute_eval (clock - 1) bounded_case16594_cell0_whole_combined_ceqs
    (subst
      [(«source_descriptor»,from_cv source_descriptor);
       («tree_dim»,from_cv tree_dim);(«tokens»,from_cv token_stream);
       («encoded_jobs»,from_cv encoded_jobs)]
      bounded_case16594_cell0_whole_check_body) refs
Proof
  strip_tac
  >> irule
       compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_compute_eval_literal_app4
  >> simp [bounded_case16594_cell0_whole_check_named_lookup]
QED

Theorem bounded_case16594_cell0_whole_expected_result_identity:
  bounded_case16594_cell0_whole_hol_light_result =
    Pair (Num 1)
      (Pair (Num 1)
        (Pair (Num 0)
          (Pair bounded_case16594_cell0_whole_job_metadata (Num 0))))
Proof
  rw
    [compute_boundedCase16594Cell0WholeHolLightDataTheory.bounded_case16594_cell0_whole_hol_light_result_def,
     compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_job_metadata_def]
QED

Theorem bounded_case16594_cell0_whole_final_pair_eval:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 12 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (Pair
      (App «candle_cv_q_packed_object_whole_jobs_check»
        [from_cv bounded_case16594_cell0_whole_plan_codes;
         from_cv bounded_case16594_cell0_whole_source_instructions;
         from_cv
           (Pair bounded_case16594_cell0_whole_packed_cell (Num 0));
         from_cv bounded_case16594_cell0_whole_encoded_jobs])
      (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv bounded_case16594_cell0_whole_tree_dim;
         from_cv bounded_case16594_cell0_whole_tokens;
         from_cv bounded_case16594_cell0_whole_encoded_jobs;Num 0]))
    (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_cell0_whole_hol_light_result),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_cell0_whole_expected_result_identity]
  >> irule
       (Q.INST
          [`left_result` |-> `Num 1`,
           `right_result` |->
             `Pair (Num 1)
                (Pair (Num 0)
                  (Pair bounded_case16594_cell0_whole_job_metadata
                    (Num 0)))`]
          compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
        |> SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def])
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_encoded_jobs_shape]
      >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
      >> rw
           [compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_nil_tails]
      >> irule
           (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
             compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_jobs_singleton_eval_clock)
      >> intLib.ARITH_TAC)
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594Cell0WholeCompactRunEvalTheory.bounded_case16594_cell0_whole_compact_run_singleton_eval)
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_cell0_whole_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_runtime_cell0_codes_cv + 20 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
      bounded_case16594_cell0_whole_hol_light_entry (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_cell0_whole_hol_light_result),refs)
Proof
  strip_tac
  >> rw
       [compute_boundedCase16594Cell0WholePayloadsTheory.bounded_case16594_cell0_whole_entry_from_payloads]
  >> rw [bounded_case16594_cell0_whole_check_unfold]
  >> simp
       [bounded_case16594_cell0_whole_check_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_cell0_whole_plan_codes`
  >> conj_tac
  >- simp
       [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_source_descriptor_shape,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair bounded_case16594_cell0_whole_source_instructions
          (Pair bounded_case16594_cell0_whole_packed_cell (Num 0))`
  >> conj_tac
  >- simp
       [compute_boundedCase16594Cell0WholeStructureTheory.bounded_case16594_cell0_whole_source_descriptor_shape,
        compute_boundedCase16594Cell0WholeJobsEvalTheory.bounded_case16594_cell0_whole_nil_tails,
        compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_cell0_whole_source_instructions`
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_fst_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `Pair bounded_case16594_cell0_whole_packed_cell (Num 0)`
  >> conj_tac
  >- simp
       [compute_execTheory.from_cv_def,
        Once compute_evalTheory.compute_eval_def,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp [compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         bounded_case16594_cell0_whole_final_pair_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
