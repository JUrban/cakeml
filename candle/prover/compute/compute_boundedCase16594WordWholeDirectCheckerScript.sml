(*****************************************************************************
 * Complete case-16594 checker with the proved direct topology executor.     *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeDirectChecker
Ancestors
  compute_boundedCase16594WordWholeJobsChecker
  compute_boundedCase16594WordDirectTopologyRunRefinement
  compute_boundedCase16594WordWholeChecker
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_whole_direct_checker_def:
  bounded_case16594_word_whole_direct_checker certificate source_descriptor
      tree_dim token_stream encoded_jobs =
    if bounded_case16594_word_whole_jobs_checker certificate
         source_descriptor encoded_jobs
    then
      case bounded_case16594_direct_topology_result tree_dim token_stream
          encoded_jobs of
      | NONE => NONE
      | SOME topology_result => SOME (Pair (Num 1) topology_result)
    else NONE
End

Theorem bounded_case16594_word_whole_direct_checker_contract:
  bounded_case16594_word_whole_direct_checker certificate source_descriptor
      tree_dim token_stream encoded_jobs = SOME result ==>
  ?packed_cells dimension remaining_jobs final_stack.
    source_descriptor =
      Pair bounded_case16594_generic_prefix167_codes_cv
        (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells) /\
    bounded_case16594_word_whole_jobs_checker certificate
      source_descriptor encoded_jobs /\
    tree_dim = Num dimension /\
    bounded_case16594_direct_topology_run dimension token_stream
      encoded_jobs (Num 0) = SOME (remaining_jobs,final_stack) /\
    result =
      Pair (Num 1)
        (Pair (Num 1) (Pair remaining_jobs final_stack))
Proof
  rw [bounded_case16594_word_whole_direct_checker_def]
  >> every_case_tac
  >> gvs
       [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_result_def]
  >> imp_res_tac
       compute_boundedCase16594WordWholeJobsCheckerTheory.bounded_case16594_word_whole_jobs_checker_contract
  >> gvs []
  >> Cases_on `tree_dim`
  >> fs
       [compute_boundedCase16594WordDirectTopologyTheory.bounded_case16594_direct_topology_result_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case16594_word_whole_direct_checker_pair_eval:
  bounded_case16594_word_whole_direct_checker certificate
      (Pair bounded_case16594_generic_prefix167_codes_cv
        (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells))
      (Num dimension) token_stream encoded_jobs = SOME result /\
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 875 + 12 < clock /\
  bounded_case16594_direct_cv_list_length token_stream *
      (dimension + 42) + 4 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (Pair
      (App «candle_cv_q_packed_object_whole_jobs_check»
        [from_cv bounded_case16594_generic_prefix167_codes_cv;
         from_cv bounded_case16594_generic_prefix167_sources_cv;
         from_cv packed_cells;from_cv encoded_jobs])
      (bounded_case16594_word_topology_expression
        (Num dimension) token_stream encoded_jobs))
    (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> imp_res_tac bounded_case16594_word_whole_direct_checker_contract
  >> gvs []
  >> irule
       (Q.INST
          [`left_result` |-> `Num 1`,
           `right_result` |->
             `Pair (Num 1) (Pair remaining_jobs final_stack)`]
          compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
        |> SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def])
  >> conj_tac
  >- (sg
        `bounded_case16594_word_whole_jobs_checker certificate
           (Pair bounded_case16594_generic_prefix167_codes_cv
             (Pair bounded_case16594_generic_prefix167_sources_cv
               packed_cells)) encoded_jobs /\
         524405 +
             2 * bounded_case16594_object_cv_list_length
               bounded_case16594_generic_prefix167_codes_cv + 875 + 12 <
           clock`
      >- (conj_tac >- asm_rewrite_tac [] >> intLib.ARITH_TAC)
      >> imp_res_tac
           compute_boundedCase16594WordWholeJobsCheckerTheory.bounded_case16594_word_whole_jobs_checker_eval_clock
      >> asm_rewrite_tac []
      >> simp [compute_execTheory.from_cv_def])
  >> rw
       [compute_boundedCase16594WordWholeCheckerTheory.bounded_case16594_word_topology_expression_def]
  >> irule
       (Q.SPECL
          [`dimension`,`token_stream`,`encoded_jobs`,`Num 0`,
           `remaining_jobs`,`final_stack`,`clock`,`refs`]
          compute_boundedCase16594WordDirectTopologyRunRefinementTheory.bounded_case16594_direct_topology_run_eval
        |> SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def])
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
