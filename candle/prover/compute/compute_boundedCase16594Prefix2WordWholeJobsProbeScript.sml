(*****************************************************************************
 * Genuine two-cell production-shape probe for case 16594.                   *
 *                                                                           *
 * Cells 1 and 2 were independently authenticated by the prefix-4 word       *
 * theories.  Here the generic producer recomputes each exact 134-packet      *
 * payload from its 31 typed certificates, both ordinary whole jobs pass,     *
 * and the unchanged recursive jobs wrapper accepts the two-cell list.        *
 *****************************************************************************)
Theory compute_boundedCase16594Prefix2WordWholeJobsProbe
Ancestors
  compute_boundedCase16594WordWholeJobsProducer
  compute_boundedCase16594Prefix4WordConvertedEntryEval
Libs
  bossLib preamble intLib

open compute_boundedCase16594Prefix4WordConvertedEntryEvalTheory
open compute_boundedCase16594Prefix4WordPacketContractsTheory

Theorem bounded_case16594_prefix4_cell1_word_entry_produce_exact:
  bounded_case16594_word_entry_produce
      bounded_case16594_prefix4_cell1_word_radii
      bounded_case16594_prefix4_cell1_word_center_boxes
      bounded_case16594_prefix4_cell1_word_outer_boxes
      bounded_case16594_prefix4_cell1_word_certificates =
    SOME
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv
          bounded_case16594_prefix4_cell1_word_runtime_packets))
Proof
  rw
    [compute_boundedCase16594WordEntryProducerTheory.bounded_case16594_word_entry_produce_def,
     bounded_case16594_prefix4_cell1_word_radii_length,
     bounded_case16594_prefix4_cell1_word_center_boxes_length,
     bounded_case16594_prefix4_cell1_word_outer_boxes_length,
     bounded_case16594_prefix4_cell1_word_center_boxes_valid,
     bounded_case16594_prefix4_cell1_word_outer_boxes_valid,
     bounded_case16594_prefix4_cell1_word_radius_pairs,
     bounded_case16594_prefix4_cell1_word_runtime_trace_call_exact,
     bounded_case16594_prefix4_cell1_word_dispatch_packet_contracts,
     bounded_case16594_prefix4_cell1_word_result_accepts]
QED

Theorem bounded_case16594_prefix4_cell2_word_entry_produce_exact:
  bounded_case16594_word_entry_produce
      bounded_case16594_prefix4_cell2_word_radii
      bounded_case16594_prefix4_cell2_word_center_boxes
      bounded_case16594_prefix4_cell2_word_outer_boxes
      bounded_case16594_prefix4_cell2_word_certificates =
    SOME
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv
          bounded_case16594_prefix4_cell2_word_runtime_packets))
Proof
  rw
    [compute_boundedCase16594WordEntryProducerTheory.bounded_case16594_word_entry_produce_def,
     bounded_case16594_prefix4_cell2_word_radii_length,
     bounded_case16594_prefix4_cell2_word_center_boxes_length,
     bounded_case16594_prefix4_cell2_word_outer_boxes_length,
     bounded_case16594_prefix4_cell2_word_center_boxes_valid,
     bounded_case16594_prefix4_cell2_word_outer_boxes_valid,
     bounded_case16594_prefix4_cell2_word_radius_pairs,
     bounded_case16594_prefix4_cell2_word_runtime_trace_call_exact,
     bounded_case16594_prefix4_cell2_word_dispatch_packet_contracts,
     bounded_case16594_prefix4_cell2_word_result_accepts]
QED

Definition bounded_case16594_prefix4_cell1_word_runtime_certificates_def:
  bounded_case16594_prefix4_cell1_word_runtime_certificates =
    bounded_object_q_cv_list
      (MAP bounded_interval64_object_q_cv
        bounded_case16594_prefix4_cell1_word_runtime_packets)
End

Definition bounded_case16594_prefix4_cell2_word_runtime_certificates_def:
  bounded_case16594_prefix4_cell2_word_runtime_certificates =
    bounded_object_q_cv_list
      (MAP bounded_interval64_object_q_cv
        bounded_case16594_prefix4_cell2_word_runtime_packets)
End

Theorem bounded_case16594_prefix4_cell1_word_whole_job_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_case16594_word_whole_packed_cell
           bounded_case16594_prefix4_cell1_word_radii
           bounded_case16594_prefix4_cell1_word_runtime_certificates);
       from_cv
         (bounded_case16594_word_whole_job
           bounded_case16594_prefix4_cell1_word_center_boxes
           bounded_case16594_prefix4_cell1_word_outer_boxes source_box)])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_produce_eval_clock)
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `bounded_case16594_prefix4_cell1_word_certificates`
  >> rw
       [bounded_case16594_prefix4_cell1_word_entry_produce_exact,
        bounded_case16594_prefix4_cell1_word_runtime_certificates_def]
QED

Theorem bounded_case16594_prefix4_cell2_word_whole_job_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_case16594_word_whole_packed_cell
           bounded_case16594_prefix4_cell2_word_radii
           bounded_case16594_prefix4_cell2_word_runtime_certificates);
       from_cv
         (bounded_case16594_word_whole_job
           bounded_case16594_prefix4_cell2_word_center_boxes
           bounded_case16594_prefix4_cell2_word_outer_boxes source_box)])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_produce_eval_clock)
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `bounded_case16594_prefix4_cell2_word_certificates`
  >> rw
       [bounded_case16594_prefix4_cell2_word_entry_produce_exact,
        bounded_case16594_prefix4_cell2_word_runtime_certificates_def]
QED

Definition bounded_case16594_prefix2_word_packed_cells_def:
  bounded_case16594_prefix2_word_packed_cells =
    Pair
      (bounded_case16594_word_whole_packed_cell
        bounded_case16594_prefix4_cell1_word_radii
        bounded_case16594_prefix4_cell1_word_runtime_certificates)
      (Pair
        (bounded_case16594_word_whole_packed_cell
          bounded_case16594_prefix4_cell2_word_radii
          bounded_case16594_prefix4_cell2_word_runtime_certificates)
        (Num 0))
End

Definition bounded_case16594_prefix2_word_jobs_def:
  bounded_case16594_prefix2_word_jobs source_box1 source_box2 =
    Pair
      (bounded_case16594_word_whole_job
        bounded_case16594_prefix4_cell1_word_center_boxes
        bounded_case16594_prefix4_cell1_word_outer_boxes source_box1)
      (Pair
        (bounded_case16594_word_whole_job
          bounded_case16594_prefix4_cell2_word_center_boxes
          bounded_case16594_prefix4_cell2_word_outer_boxes source_box2)
        (Num 0))
End

Theorem bounded_case16594_prefix2_word_whole_jobs_eval_clock:
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 10 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_jobs_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv bounded_case16594_prefix2_word_packed_cells;
       from_cv
         (bounded_case16594_prefix2_word_jobs source_box1 source_box2)])
    (refs:hol_refs) = (M_success (Num 1),refs)
Proof
  strip_tac
  >> PURE_REWRITE_TAC
       [bounded_case16594_prefix2_word_packed_cells_def,
        bounded_case16594_prefix2_word_jobs_def]
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule bounded_case16594_prefix4_cell1_word_whole_job_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_cons_eval
  >> rpt conj_tac
  >- intLib.ARITH_TAC
  >- (irule bounded_case16594_prefix4_cell2_word_whole_job_eval_clock
      >> intLib.ARITH_TAC)
  >> irule
       compute_boundedCase16594WordWholeJobsProducerTheory.bounded_case16594_word_whole_jobs_empty_eval
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
