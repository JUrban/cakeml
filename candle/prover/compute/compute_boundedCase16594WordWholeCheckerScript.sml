(*****************************************************************************
 * Complete production callback checker for the case-16594 whole call.      *
 *                                                                           *
 * The fixed-word matcher discharges the expensive numerical jobs from the  *
 * external certificate.  Only the compact topology expression is evaluated *
 * by the generic pure evaluator.  The refinement theorem below composes     *
 * both results back into the unchanged ordinary four-argument whole call.   *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeChecker
Ancestors
  compute_boundedCase16594WordWholeJobsChecker
  compute_evalPure
  compute_pureFast
  compute_boundedCase16594Cell0WholeEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_topology_fuel_def:
  (bounded_case16594_word_topology_fuel:num) = 1000000
End

Definition bounded_case16594_word_topology_expression_def:
  bounded_case16594_word_topology_expression tree_dim token_stream encoded_jobs =
    App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
      [from_cv tree_dim;from_cv token_stream;from_cv encoded_jobs;Num 0]
End

Definition bounded_case16594_word_whole_checker_def:
  bounded_case16594_word_whole_checker certificate source_descriptor
      tree_dim token_stream encoded_jobs =
    if bounded_case16594_word_whole_jobs_checker certificate
         source_descriptor encoded_jobs
    then
      case compute_eval_pure bounded_case16594_word_topology_fuel
          bounded_case16594_cell0_whole_combined_ceqs
          (bounded_case16594_word_topology_expression
            tree_dim token_stream encoded_jobs) of
      | NONE => NONE
      | SOME topology_expression_result =>
          (case compute_exp_to_cv topology_expression_result of
           | NONE => NONE
           | SOME topology_result => SOME (Pair (Num 1) topology_result))
    else NONE
End

Theorem bounded_case16594_word_whole_checker_contract:
  bounded_case16594_word_whole_checker certificate source_descriptor
      tree_dim token_stream encoded_jobs = SOME result ==>
  ?packed_cells topology_expression_result topology_result.
    source_descriptor =
      Pair bounded_case16594_generic_prefix167_codes_cv
        (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells) /\
    bounded_case16594_word_whole_jobs_checker certificate
      source_descriptor encoded_jobs /\
    compute_eval_pure bounded_case16594_word_topology_fuel
      bounded_case16594_cell0_whole_combined_ceqs
      (bounded_case16594_word_topology_expression
        tree_dim token_stream encoded_jobs) =
          SOME topology_expression_result /\
    compute_exp_to_cv topology_expression_result = SOME topology_result /\
    result = Pair (Num 1) topology_result
Proof
  rw [bounded_case16594_word_whole_checker_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedCase16594WordWholeJobsCheckerTheory.bounded_case16594_word_whole_jobs_checker_contract
  >> gvs []
QED

Theorem bounded_case16594_word_whole_checker_pair_eval:
  bounded_case16594_word_whole_checker certificate
      (Pair bounded_case16594_generic_prefix167_codes_cv
        (Pair bounded_case16594_generic_prefix167_sources_cv packed_cells))
      tree_dim token_stream encoded_jobs = SOME result /\
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 875 + 12 < clock /\
  bounded_case16594_word_topology_fuel <= clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (Pair
      (App «candle_cv_q_packed_object_whole_jobs_check»
        [from_cv bounded_case16594_generic_prefix167_codes_cv;
         from_cv bounded_case16594_generic_prefix167_sources_cv;
         from_cv packed_cells;from_cv encoded_jobs])
      (bounded_case16594_word_topology_expression
        tree_dim token_stream encoded_jobs))
    (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> imp_res_tac bounded_case16594_word_whole_checker_contract
  >> imp_res_tac compute_pureFastTheory.compute_exp_to_cv_sound
  >> gvs []
  >> irule
       (Q.INST
          [`left_result` |-> `Num 1`,
           `right_result` |-> `topology_result`]
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
  >> irule compute_evalPureTheory.compute_eval_pure_refines
  >> qexists_tac `bounded_case16594_word_topology_fuel`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_word_whole_checker_eval_clock:
  bounded_case16594_word_whole_checker certificate source_descriptor
      tree_dim token_stream encoded_jobs = SOME result /\
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 875 + 20 < clock /\
  bounded_case16594_word_topology_fuel + 20 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_check»
      [from_cv source_descriptor;from_cv tree_dim;
       from_cv token_stream;from_cv encoded_jobs])
    (refs:hol_refs) = (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> imp_res_tac bounded_case16594_word_whole_checker_contract
  >> qpat_x_assum `source_descriptor = _` SUBST_ALL_TAC
  >> qpat_x_assum `result = _` SUBST_ALL_TAC
  >> rw
       [compute_boundedCase16594Cell0WholeEvalTheory.bounded_case16594_cell0_whole_check_unfold]
  >> simp
       [compute_boundedCase16594Cell0WholeEvalTheory.bounded_case16594_cell0_whole_check_body_def,
        compute_evalTheory.subst_def,compute_execProofTheory.subst_from_cv]
  >> irule
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_generic_prefix167_codes_cv`
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
       `Pair bounded_case16594_generic_prefix167_sources_cv packed_cells`
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
       compute_boundedCase16594ObjectDispatchProgramTraceEvalTheory.bounded_case16594_object_compute_eval_let_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_case16594_generic_prefix167_sources_cv`
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
  >> qexists_tac `packed_cells`
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
  >> sg
       `bounded_case16594_word_whole_checker certificate
          (Pair bounded_case16594_generic_prefix167_codes_cv
            (Pair bounded_case16594_generic_prefix167_sources_cv
              packed_cells)) tree_dim token_stream encoded_jobs =
            SOME (Pair (Num 1) topology_result) /\
        524405 +
            2 * bounded_case16594_object_cv_list_length
              bounded_case16594_generic_prefix167_codes_cv + 875 + 12 <
          clock - 5 /\
        bounded_case16594_word_topology_fuel <= clock - 5`
  >- (rpt conj_tac >- asm_rewrite_tac [] >> intLib.ARITH_TAC)
  >> imp_res_tac bounded_case16594_word_whole_checker_pair_eval
  >> qpat_x_assum `!state. _` (qspec_then `refs` assume_tac)
  >> fs
       [bounded_case16594_word_topology_expression_def,
        compute_execTheory.from_cv_def]
QED

Theorem bounded_case16594_word_whole_checker_rejects_bad_numerical_payload:
  ~bounded_case16594_word_whole_jobs_checker certificate source_descriptor
      encoded_jobs ==>
  bounded_case16594_word_whole_checker certificate source_descriptor
    tree_dim token_stream encoded_jobs = NONE
Proof
  simp [bounded_case16594_word_whole_checker_def]
QED

Theorem bounded_case16594_word_whole_checker_rejects_topology_failure:
  compute_eval_pure bounded_case16594_word_topology_fuel
      bounded_case16594_cell0_whole_combined_ceqs
      (bounded_case16594_word_topology_expression
        tree_dim token_stream encoded_jobs) = NONE ==>
  bounded_case16594_word_whole_checker certificate source_descriptor
    tree_dim token_stream encoded_jobs = NONE
Proof
  simp [bounded_case16594_word_whole_checker_def]
QED

val _ = export_theory ();
