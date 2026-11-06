(*****************************************************************************
 * Generic fixed-word producer for one case-16594 ordinary object entry.
 *
 * The production fast evaluator must not trust the 134 object-q packet
 * intervals carried by the ordinary Candle call.  It recomputes those
 * packets from the six word radii, the word center/outer boxes, and the 31
 * typed scalar certificates.  Acceptance returns the exact object-q packet
 * payload whose ordinary evaluator result is justified by G3.
 *
 * No genuine-cell constant occurs in this theory.  The closed cell theories
 * remain regression evidence only; this producer is the reusable callback
 * step required by the production route.
 *****************************************************************************)
Theory compute_boundedCase16594WordEntryProducer
Ancestors
  compute_boundedCase16594WordConvertedAcceptedEntryEval
Libs
  bossLib preamble

Definition bounded_case16594_word_entry_produce_def:
  bounded_case16594_word_entry_produce word_radii word_center_boxes
      word_outer_boxes word_certificates =
    if LENGTH word_radii = 6 /\
       LENGTH word_center_boxes = 6 /\
       LENGTH word_outer_boxes = 6 /\
       EVERY bounded_interval64_valid word_center_boxes /\
       EVERY bounded_interval64_valid word_outer_boxes
    then
      case bounded_taylor_radius_pairs word_radii of
      | NONE => NONE
      | SOME weights =>
          case bounded_analytic64_program_runtime_certificate_trace
            word_radii word_center_boxes word_outer_boxes
            bounded_case16594_prepared_program ([],word_certificates) of
          | SOME (([word_result],[]),packets) =>
              if bounded_case16594_word_dispatch_packet_contracts
                   word_certificates packets /\
                 bounded_packed_analytic_result_accepts word_result
              then
                SOME
                  (bounded_object_q_cv_list
                    (MAP bounded_interval64_object_q_cv packets))
              else NONE
          | _ => NONE
    else NONE
End

Theorem bounded_case16594_word_entry_produce_eval:
  bounded_case16594_word_entry_produce word_radii word_center_boxes
      word_outer_boxes word_certificates = SOME runtime_certificates ==>
  compute_eval compute_default_clock
    bounded_case16594_object_dispatch_cell0_ceqs
    (App «candle_cv_q_packed_object_dispatch_entry»
      [from_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv word_center_boxes));
       from_cv
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv word_outer_boxes));
       from_cv
        (bounded_object_q_cv_list
          (MAP bounded_word64_object_q_cv word_radii));
       from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv runtime_certificates])
    (refs:hol_refs) =
      (M_success (from_cv (Num 1)),refs)
Proof
  rw [bounded_case16594_word_entry_produce_def]
  >> every_case_tac
  >> gvs []
  >> once_rewrite_tac
       [GSYM
          (SPEC ``(1:num)``
            (CONJUNCT1 compute_execTheory.from_cv_def))]
  >> irule
       compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_complete_accepted_entry_eval
  >> asm_rewrite_tac
       [compute_boundedCase16594WordConvertedAcceptedEntryEvalTheory.bounded_case16594_word_converted_default_clock_capacity]
  >> metis_tac []
QED

Theorem bounded_case16594_word_entry_produce_packets:
  bounded_case16594_word_entry_produce word_radii word_center_boxes
      word_outer_boxes word_certificates = SOME runtime_certificates ==>
  ?weights word_result packets.
    bounded_taylor_radius_pairs word_radii = SOME weights /\
    bounded_analytic64_program_runtime_certificate_trace word_radii
      word_center_boxes word_outer_boxes bounded_case16594_prepared_program
      ([],word_certificates) = SOME (([word_result],[]),packets) /\
    bounded_case16594_word_dispatch_packet_contracts
      word_certificates packets /\
    bounded_packed_analytic_result_accepts word_result /\
    runtime_certificates =
      bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv packets)
Proof
  rw [bounded_case16594_word_entry_produce_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac []
QED

val _ = export_theory ();
