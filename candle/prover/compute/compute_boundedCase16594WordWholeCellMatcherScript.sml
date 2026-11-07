(*****************************************************************************
 * Generic data matcher for one case-16594 packed-object whole-call cell.    *
 *                                                                           *
 * The external fixed-word witness supplies the outer box, center box, six   *
 * radii, and 31 typed scalar certificates.  The ordinary Candle call        *
 * independently supplies its encoded radii, generated runtime packets, and  *
 * job.  A hit is possible only when all shared fields agree exactly and the  *
 * generic G3 producer recomputes the exact runtime packet payload.           *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeCellMatcher
Ancestors
  compute_boundedCase16594WordWholeJobProducer
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_whole_cell_match_def:
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      packed_cell job =
    case packed_cell of
    | Pair encoded_radii runtime_certificates =>
        (case job of
         | Pair encoded_outer_boxes center_and_source =>
             (case center_and_source of
              | Pair encoded_center_boxes source_box =>
                  if encoded_radii =
                       bounded_object_q_cv_list
                         (MAP bounded_word64_object_q_cv word_radii) /\
                     encoded_outer_boxes =
                       bounded_object_q_cv_list
                         (MAP bounded_interval64_object_q_cv
                           word_outer_boxes) /\
                     encoded_center_boxes =
                       bounded_object_q_cv_list
                         (MAP bounded_interval64_object_q_cv
                           word_center_boxes)
                  then
                    case bounded_case16594_word_entry_produce word_radii
                        word_center_boxes word_outer_boxes
                        word_certificates of
                    | NONE => NONE
                    | SOME produced_runtime_certificates =>
                        if runtime_certificates =
                             produced_runtime_certificates
                        then SOME source_box
                        else NONE
                  else NONE
              | _ => NONE)
         | _ => NONE)
    | _ => NONE
End

Theorem bounded_case16594_word_whole_cell_match_contract:
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      packed_cell job = SOME source_box ==>
  ?runtime_certificates.
    bounded_case16594_word_entry_produce word_radii word_center_boxes
      word_outer_boxes word_certificates = SOME runtime_certificates /\
    packed_cell =
      bounded_case16594_word_whole_packed_cell
        word_radii runtime_certificates /\
    job =
      bounded_case16594_word_whole_job
        word_center_boxes word_outer_boxes source_box
Proof
  simp
    [bounded_case16594_word_whole_cell_match_def,
     compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_packed_cell_def,
     compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_case16594_word_whole_cell_match_eval_clock:
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      packed_cell job = SOME source_box /\
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv packed_cell;from_cv job])
    (refs:hol_refs) = (M_success (from_cv (Num 1)),refs)
Proof
  strip_tac
  >> imp_res_tac bounded_case16594_word_whole_cell_match_contract
  >> gvs []
  >> irule
       (SIMP_RULE (srw_ss()) [compute_execTheory.from_cv_def]
         compute_boundedCase16594WordWholeJobProducerTheory.bounded_case16594_word_whole_job_produce_eval_clock)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `word_certificates`
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_word_whole_cell_match_rejects_radii:
  encoded_radii <>
      bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv word_radii) ==>
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      (Pair encoded_radii runtime_certificates)
      (Pair encoded_outer_boxes (Pair encoded_center_boxes source_box)) = NONE
Proof
  simp [bounded_case16594_word_whole_cell_match_def]
QED

Theorem bounded_case16594_word_whole_cell_match_rejects_outer_boxes:
  encoded_outer_boxes <>
      bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv word_outer_boxes) ==>
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      (Pair encoded_radii runtime_certificates)
      (Pair encoded_outer_boxes (Pair encoded_center_boxes source_box)) = NONE
Proof
  simp [bounded_case16594_word_whole_cell_match_def]
QED

Theorem bounded_case16594_word_whole_cell_match_rejects_center_boxes:
  encoded_center_boxes <>
      bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv word_center_boxes) ==>
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      (Pair encoded_radii runtime_certificates)
      (Pair encoded_outer_boxes (Pair encoded_center_boxes source_box)) = NONE
Proof
  simp [bounded_case16594_word_whole_cell_match_def]
QED

Theorem bounded_case16594_word_whole_cell_match_rejects_runtime_packets:
  bounded_case16594_word_entry_produce word_radii word_center_boxes
      word_outer_boxes word_certificates = SOME produced_runtime_certificates /\
  runtime_certificates <> produced_runtime_certificates ==>
  bounded_case16594_word_whole_cell_match
      ((word_outer_boxes,word_center_boxes,word_radii),word_certificates)
      (Pair
        (bounded_object_q_cv_list
          (MAP bounded_word64_object_q_cv word_radii))
        runtime_certificates)
      (Pair
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv word_outer_boxes))
        (Pair
          (bounded_object_q_cv_list
            (MAP bounded_interval64_object_q_cv word_center_boxes))
          source_box)) = NONE
Proof
  simp [bounded_case16594_word_whole_cell_match_def]
QED

val _ = export_theory ();
