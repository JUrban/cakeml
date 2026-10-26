(*****************************************************************************
 * Tag-10 registered evaluator control semantics for the paired historical
 * program loop.  The loop body is unchanged from the historical registration;
 * only the authenticated equation environment differs.  Keep these theorems
 * additive so the existing tag-9 input and certificate theories remain valid.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10HistProgramRunEval
Ancestors
  compute_registeredCase10173HistoricalChunk16Tag10Data
  compute_registeredCase10173HistProgramRunEval
Libs
  bossLib preamble

Theorem registered_case10173_tag10_hist_program_run_lookup:
  ALOOKUP registered_case10173_historical_chunk16_tag10_ceqs
      «candle_cv_case10173_hist_program_run» =
    SOME
      ([«center_boxes»;«boxes»;«radii»;«roots»;
        «center_program»;«box_program»;«stack»],
       registered_case10173_hist_program_run_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_tag10_hist_program_run_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv stack])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (subst
        [(«center_boxes»,from_cv center_boxes);(«boxes»,from_cv boxes);
         («radii»,from_cv radii);(«roots»,from_cv roots);
         («center_program»,from_cv center_program);
         («box_program»,from_cv box_program);(«stack»,from_cv stack)]
        registered_case10173_hist_program_run_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_literal_app7
  >> simp [registered_case10173_tag10_hist_program_run_lookup]
QED

Theorem registered_case10173_tag10_hist_program_run_center_nil_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Num center_nil);from_cv box_program;from_cv stack])
      (refs:hol_refs) =
    (M_success (from_cv stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_program_run_unfold]
  >> simp
       [registered_case10173_hist_program_run_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_hist_program_run_box_nil_eval:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Pair center_instruction center_program);
         from_cv (Num box_nil);from_cv stack]) (refs:hol_refs) =
    (M_success (from_cv stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_program_run_unfold]
  >> simp
       [registered_case10173_hist_program_run_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_evalTheory.compute_eval_def,
        compute_execProofTheory.compute_eval_from_cv,
        compute_evalTheory.do_uop_def,
        compute_evalTheory.do_ispair_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_tag10_hist_program_run_cons_eval:
  1 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_step»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_instruction;from_cv box_instruction;from_cv stack])
      (refs:hol_refs) =
      (M_success (from_cv next_stack),refs) /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv next_stack]) refs =
      (M_success (from_cv final_stack),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv (Pair center_instruction center_program);
         from_cv (Pair box_instruction box_program);from_cv stack]) refs =
    (M_success (from_cv final_stack),refs)
Proof
  strip_tac
  >> simp [registered_case10173_tag10_hist_program_run_unfold]
  >> simp
       [registered_case10173_hist_program_run_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv,
        compute_registeredCase10173CanonicalListEvalTheory.compute_eval_if_ispair_from_cv_components]
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_step»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           Uop Fst (Pair (from_cv center_instruction)
             (from_cv center_program));
           Uop Fst (Pair (from_cv box_instruction) (from_cv box_program));
           from_cv stack]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_step»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           from_cv center_instruction;from_cv box_instruction;from_cv stack])
        refs` by
       (irule
          compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_app7_argument_results
        >> fs
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_fst_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv])
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           Uop Snd (from_cv (Pair center_instruction center_program));
           Uop Snd (from_cv (Pair box_instruction box_program));
           App «candle_cv_case10173_hist_step»
             [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
              Uop Fst (from_cv (Pair center_instruction center_program));
              Uop Fst (from_cv (Pair box_instruction box_program));
              from_cv stack]]) refs =
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_program_run»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
           from_cv center_program;from_cv box_program;from_cv next_stack]) refs` by
        (irule
           compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_app7_argument_results
        >> fs
             [compute_registeredCase10173CanonicalEvalTheory.compute_eval_uop_snd_from_cv_components,
              compute_execProofTheory.compute_eval_from_cv])
  >> fs []
QED

val _ = export_theory ();
