(*****************************************************************************
 * Four genuine case-16594 cells through the complete ordinary whole call.  *
 *                                                                           *
 * Each numerical job is discharged by the generic word producer theorem.   *
 * The same exact jobs then pass the genuine seven-token topology probe, and *
 * the two results are composed through the unchanged production whole-call  *
 * wrapper.  This is a bounded vertical slice before the 875-cell fixture.    *
 *****************************************************************************)
Theory compute_boundedCase16594Prefix4WholeCallProbe
Ancestors
  compute_boundedCase16594Prefix4ActualWholeTopologyProbe
  compute_boundedCase16594Prefix2WordWholeJobsProbe
  compute_boundedCase16594Cell0WholeEval
Libs
  bossLib preamble intLib

open compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory
open compute_boundedCase16594Prefix4WordPacketContractsTheory

Theorem bounded_case16594_prefix4_cell3_word_entry_produce_exact:
  bounded_case16594_word_entry_produce
      bounded_case16594_prefix4_cell3_word_radii
      bounded_case16594_prefix4_cell3_word_center_boxes
      bounded_case16594_prefix4_cell3_word_outer_boxes
      bounded_case16594_prefix4_cell3_word_certificates =
    SOME
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv
          bounded_case16594_prefix4_cell3_word_runtime_packets))
Proof
  rw
    [compute_boundedCase16594WordEntryProducerTheory.bounded_case16594_word_entry_produce_def,
     bounded_case16594_prefix4_cell3_word_radii_length,
     bounded_case16594_prefix4_cell3_word_center_boxes_length,
     bounded_case16594_prefix4_cell3_word_outer_boxes_length,
     bounded_case16594_prefix4_cell3_word_center_boxes_valid,
     bounded_case16594_prefix4_cell3_word_outer_boxes_valid,
     bounded_case16594_prefix4_cell3_word_radius_pairs,
     bounded_case16594_prefix4_cell3_word_runtime_trace_call_exact,
     bounded_case16594_prefix4_cell3_word_dispatch_packet_contracts,
     bounded_case16594_prefix4_cell3_word_result_accepts]
QED

Definition bounded_case16594_prefix4_cell3_word_runtime_certificates_def:
  bounded_case16594_prefix4_cell3_word_runtime_certificates =
    bounded_object_q_cv_list
      (MAP bounded_interval64_object_q_cv
        bounded_case16594_prefix4_cell3_word_runtime_packets)
End

Theorem bounded_case16594_prefix4_cell0_word_whole_job_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_case16594_word_whole_packed_cell
           bounded_case16594_cell0_source_word_radii
           bounded_case16594_cell0_fast_object_certificates_cv);
       from_cv
         (bounded_case16594_word_whole_job
           bounded_case16594_cell0_source_word_center_environment
           bounded_case16594_cell0_authenticated_word_box_environment
           source_box)])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_produce_eval_clock)
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `bounded_case16594_cell0_source_word_certificates`
  >> rw
       [compute_boundedCase16594Cell0WordEntryProducerTheory.bounded_case16594_cell0_word_entry_produce_exact]
QED

Theorem bounded_case16594_prefix4_cell3_word_whole_job_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_case16594_word_whole_packed_cell
           bounded_case16594_prefix4_cell3_word_radii
           bounded_case16594_prefix4_cell3_word_runtime_certificates);
       from_cv
         (bounded_case16594_word_whole_job
           bounded_case16594_prefix4_cell3_word_center_boxes
           bounded_case16594_prefix4_cell3_word_outer_boxes source_box)])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_produce_eval_clock)
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `bounded_case16594_prefix4_cell3_word_certificates`
  >> rw
       [bounded_case16594_prefix4_cell3_word_entry_produce_exact,
        bounded_case16594_prefix4_cell3_word_runtime_certificates_def]
QED

Definition bounded_case16594_prefix4_word_packed_cells_def:
  bounded_case16594_prefix4_word_packed_cells =
    Pair
      (bounded_case16594_word_whole_packed_cell
        bounded_case16594_cell0_source_word_radii
        bounded_case16594_cell0_fast_object_certificates_cv)
    (Pair
      (bounded_case16594_word_whole_packed_cell
        bounded_case16594_prefix4_cell1_word_radii
        bounded_case16594_prefix4_cell1_word_runtime_certificates)
    (Pair
      (bounded_case16594_word_whole_packed_cell
        bounded_case16594_prefix4_cell2_word_radii
        bounded_case16594_prefix4_cell2_word_runtime_certificates)
    (Pair
      (bounded_case16594_word_whole_packed_cell
        bounded_case16594_prefix4_cell3_word_radii
        bounded_case16594_prefix4_cell3_word_runtime_certificates)
      (Num 0))))
End

Theorem bounded_case16594_prefix4_word_whole_jobs_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 12 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv bounded_case16594_prefix4_word_packed_cells;
       from_cv bounded_case16594_prefix4_whole_jobs])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [bounded_case16594_prefix4_word_packed_cells_def,
        compute_boundedCase16594Prefix4WholeTopologyProbeTheory.bounded_case16594_prefix4_whole_jobs_def]
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule bounded_case16594_prefix4_cell0_word_whole_job_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule
        compute_boundedCase16594Prefix2WordWholeJobsProbeTheory.bounded_case16594_prefix4_cell1_word_whole_job_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule
        compute_boundedCase16594Prefix2WordWholeJobsProbeTheory.bounded_case16594_prefix4_cell2_word_whole_job_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule bounded_case16594_prefix4_cell3_word_whole_job_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_empty_eval
  >> intLib.ARITH_TAC
QED

Definition bounded_case16594_prefix4_word_source_descriptor_def:
  bounded_case16594_prefix4_word_source_descriptor =
    Pair bounded_case16594_generic_prefix167_codes_cv
      (Pair bounded_case16594_generic_prefix167_sources_cv
        bounded_case16594_prefix4_word_packed_cells)
End

Definition bounded_case16594_prefix4_word_whole_result_def:
  bounded_case16594_prefix4_word_whole_result =
    Pair (Num 1)
      (Pair (Num 1)
        (Pair (Num 0)
          (Pair bounded_case16594_prefix4_root_box (Num 0))))
End

Theorem bounded_case16594_prefix4_word_whole_final_pair_eval:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 12 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (Pair
      (App «candle_cv_q_packed_object_whole_jobs_check»
        [from_cv bounded_case16594_generic_prefix167_codes_cv;
         from_cv bounded_case16594_generic_prefix167_sources_cv;
         from_cv bounded_case16594_prefix4_word_packed_cells;
         from_cv bounded_case16594_prefix4_actual_whole_jobs_fast])
      (App «candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run»
        [from_cv (Num 6);
         from_cv bounded_case16594_prefix4_whole_tokens;
         from_cv bounded_case16594_prefix4_actual_whole_jobs_fast;
         from_cv (Num 0)]))
    (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_prefix4_word_whole_result),refs)
Proof
  strip_tac
  >> rw [bounded_case16594_prefix4_word_whole_result_def]
  >> irule
       (Q.INST
          [`left_result` |-> `Num 1`,
           `right_result` |->
             `Pair (Num 1)
                (Pair (Num 0)
                  (Pair bounded_case16594_prefix4_root_box (Num 0)))`]
          compute_boundedPackedObjectValueEvalTheory.bounded_packed_compute_eval_pair_from_results
        |> SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def])
  >> conj_tac
  >- (PURE_REWRITE_TAC
        [compute_boundedCase16594Prefix4ActualWholeTopologyProbeTheory.bounded_case16594_prefix4_actual_whole_jobs_fast_eq]
      >> irule bounded_case16594_prefix4_word_whole_jobs_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594Prefix4ActualWholeTopologyProbeTheory.bounded_case16594_prefix4_actual_topology_eval)
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_prefix4_word_whole_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 20 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_check»
      [from_cv bounded_case16594_prefix4_word_source_descriptor;
       from_cv (Num 6);
       from_cv bounded_case16594_prefix4_whole_tokens;
       from_cv bounded_case16594_prefix4_actual_whole_jobs_fast])
    (refs:hol_refs) =
    (M_success (from_cv bounded_case16594_prefix4_word_whole_result),refs)
Proof
  strip_tac
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
       [bounded_case16594_prefix4_word_source_descriptor_def,
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
       `Pair bounded_case16594_generic_prefix167_sources_cv
          bounded_case16594_prefix4_word_packed_cells`
  >> conj_tac
  >- simp
       [bounded_case16594_prefix4_word_source_descriptor_def,
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
  >> qexists_tac `bounded_case16594_prefix4_word_packed_cells`
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
         bounded_case16594_prefix4_word_whole_final_pair_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
