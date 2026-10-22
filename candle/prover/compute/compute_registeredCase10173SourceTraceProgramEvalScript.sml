(*****************************************************************************
 * Lift an authenticated source-program trace through the small historical
 * program wrapper.
 *
 * The numerical work remains represented by [source_program_trace].  This
 * layer performs only source splicing, structural stack-head selection, and
 * the supplied fixed-to-rational result conversion.  Its clock premise is
 * structural in the instruction count.
 *****************************************************************************)
Theory compute_registeredCase10173SourceTraceProgramEval
Ancestors
  compute_registeredCase10173CompleteSourceTraceEval
  compute_registeredCase10173HistProgramEval
  compute_registeredCase10173OrdinaryItemEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_source_trace_hist_program_eval:
  registered_case10173_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item center_source_program
      box_source_program (Num 0) (Pair item stack_tail) /\
  step_floor + item_floor +
      registered_case10173_cv_list_length center_source_program + 7 < clock /\
  compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_center_environment_list» [from_cv boxes])
      (refs:hol_refs) =
      (M_success (from_cv center_boxes),refs) /\
  compute_eval (clock - 2)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_q_fixed_list_round_upper»
        [App «candle_cv_q_radius_list» [from_cv boxes]]) refs =
      (M_success (from_cv radii),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_splice_aux»
        [Num 31;from_cv center_program]) refs =
      (M_success (from_cv center_source_program),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_splice_aux»
        [Num 31;from_cv box_program]) refs =
      (M_success (from_cv box_source_program),refs) /\
  compute_eval (clock - 3)
      registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fsa_item_to_q» [from_cv item]) refs =
      (M_success (from_cv program_result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) refs =
    (M_success (from_cv program_result),refs)
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramEvalTheory.registered_case10173_hist_program_eval_from_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `center_boxes`
  >> qexists_tac `item`
  >> qexists_tac `radii`
  >> qexists_tac `Pair item stack_tail`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (`compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_case10173_hist_program_run»
            [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
             App «candle_cv_case10173_hist_splice_aux»
               [Num 31;from_cv center_program];
             App «candle_cv_case10173_hist_splice_aux»
               [Num 31;from_cv box_program];
             Num 0]) refs =
        compute_eval (clock - 3)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_case10173_hist_program_run»
            [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
             from_cv center_source_program;from_cv box_source_program;
             from_cv (Num 0)]) refs` by
         (irule
            compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_app7_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> conj_tac >-
               simp [compute_execProofTheory.compute_eval_from_cv]
          >> conj_tac >-
               simp [compute_execProofTheory.compute_eval_from_cv]
          >> conj_tac >-
               simp [compute_execProofTheory.compute_eval_from_cv]
          >> conj_tac >-
               simp [compute_execProofTheory.compute_eval_from_cv]
          >> conj_tac >- asm_rewrite_tac []
          >> conj_tac >- asm_rewrite_tac []
          >> simp [compute_execTheory.from_cv_def,
                   compute_evalTheory.compute_eval_def,
                   ml_monadBaseTheory.st_ex_return_def])
      >> pop_assum SUBST1_TAC
      >> irule
           compute_registeredCase10173CompleteSourceTraceEvalTheory.registered_case10173_source_program_trace_sound
      >> qexists_tac `item`
      >> qexists_tac `item_floor`
      >> qexists_tac `step_floor`
      >> conj_tac >- intLib.ARITH_TAC
      >> asm_rewrite_tac [])
  >> conj_tac
  >- (irule
        compute_registeredCase10173OrdinaryItemEvalTheory.registered_case10173_fsa_item_head_cons_eval
      >> intLib.ARITH_TAC)
  >> conj_tac >- asm_rewrite_tac []
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
