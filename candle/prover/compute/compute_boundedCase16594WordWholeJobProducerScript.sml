(*****************************************************************************
 * Generic whole-job callback consequence for the fixed-word case-16594      *
 * producer.                                                                 *
 *                                                                           *
 * The trusted witness carries the six radii, center/outer boxes, and 31      *
 * typed scalar certificates.  The producer recomputes the exact 134 packet  *
 * payload consumed by the unchanged ordinary whole-job call.  This theory   *
 * proves that any successful production therefore makes that ordinary job   *
 * evaluate successfully in the combined equation environment.               *
 *****************************************************************************)
Theory compute_boundedCase16594WordWholeJobProducer
Ancestors
  compute_boundedCase16594WordEntryProducer
  compute_boundedCase16594Cell0WholeCombinedLookups
Libs
  bossLib preamble intLib

Definition bounded_case16594_word_whole_packed_cell_def:
  bounded_case16594_word_whole_packed_cell word_radii runtime_certificates =
    Pair
      (bounded_object_q_cv_list
        (MAP bounded_word64_object_q_cv word_radii))
      runtime_certificates
End

Definition bounded_case16594_word_whole_job_def:
  bounded_case16594_word_whole_job word_center_boxes word_outer_boxes
      source_box =
    Pair
      (bounded_object_q_cv_list
        (MAP bounded_interval64_object_q_cv word_outer_boxes))
      (Pair
        (bounded_object_q_cv_list
          (MAP bounded_interval64_object_q_cv word_center_boxes))
        source_box)
End

Theorem bounded_case16594_word_whole_job_check_unfold:
  5 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_case16594_word_whole_packed_cell
           word_radii runtime_certificates);
       from_cv
         (bounded_case16594_word_whole_job
           word_center_boxes word_outer_boxes source_box)])
    (refs:hol_refs) =
  compute_eval (clock - 5)
    bounded_case16594_cell0_whole_combined_ceqs
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
       from_cv runtime_certificates]) refs
Proof
  Cases_on `clock`
  >- simp []
  >> strip_tac
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        compute_boundedCase16594Cell0WholeCombinedLookupsTheory.bounded_case16594_cell0_whole_combined_whole_job_check_lookup,
        compute_evalTheory.option_def,compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.compute_eval_def,compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        bounded_case16594_word_whole_packed_cell_def,
        bounded_case16594_word_whole_job_def,
        compute_execTheory.from_cv_def,
        compute_evalTheory.do_uop_def,compute_evalTheory.do_ispair_def,
        compute_evalTheory.do_fst_def,compute_evalTheory.do_snd_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> `n - 5 = SUC n - 6` by intLib.ARITH_TAC
  >> asm_rewrite_tac []
QED

Theorem bounded_case16594_word_whole_job_produce_eval_clock:
  bounded_case16594_word_entry_produce word_radii word_center_boxes
      word_outer_boxes word_certificates = SOME runtime_certificates ==>
  524405 +
      2 * bounded_case16594_object_cv_list_length
        bounded_case16594_generic_prefix167_codes_cv + 8 < clock ==>
  compute_eval clock bounded_case16594_cell0_whole_combined_ceqs
    (App «candle_cv_q_packed_object_whole_job_check»
      [from_cv bounded_case16594_generic_prefix167_codes_cv;
       from_cv bounded_case16594_generic_prefix167_sources_cv;
       from_cv
         (bounded_case16594_word_whole_packed_cell
           word_radii runtime_certificates);
       from_cv
         (bounded_case16594_word_whole_job
           word_center_boxes word_outer_boxes source_box)])
    (refs:hol_refs) = (M_success (from_cv (Num 1)),refs)
Proof
  rpt strip_tac
  >> `5 < clock` by intLib.ARITH_TAC
  >> rw [bounded_case16594_word_whole_job_check_unfold]
  >> once_rewrite_tac
       [compute_boundedCase16594Cell0WholeCombinedEntryTheory.bounded_case16594_cell0_whole_combined_ceqs_def]
  >> irule
       (CONJUNCT1
         compute_evalCeqsAppendSuccessTheory.compute_eval_append_success)
  >> first_x_assum
       (mp_tac o
        MATCH_MP
          (Q.INST [`clock` |-> `clock - 5`]
            compute_boundedCase16594WordEntryProducerTheory.bounded_case16594_word_entry_produce_eval_clock))
  >> simp [compute_execTheory.from_cv_def]
QED

val _ = export_theory ();
