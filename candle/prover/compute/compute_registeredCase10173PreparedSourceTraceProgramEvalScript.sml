(*****************************************************************************
 * Execute a packet-parametric source trace from prepared programs.
 *
 * The underlying trace theorem exposes source-splice evaluator premises.
 * Discharge those premises here from the proved 54-instruction prepared
 * shape and the generic structural splice evaluator.  No closed first-job
 * program or numerical result is used.
 *****************************************************************************)
Theory compute_registeredCase10173PreparedSourceTraceProgramEval
Ancestors
  compute_registeredCase10173SourceTraceProgramEval
  compute_registeredCase10173ProgramSpliceEval
  compute_registeredCase10173ProgramSplicePacketEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_prepared_source_trace_hist_program_eval:
  registered_case10173_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item
      (registered_case10173_hist_splice_cv 31 center_program)
      (registered_case10173_hist_splice_cv 31 box_program)
      (Num 0) (Pair item stack_tail) /\
  registered_case10173_cv_list_length center_program = 54 /\
  registered_case10173_cv_list_length box_program = 54 /\
  step_floor + item_floor +
      registered_case10173_cv_list_length
        (registered_case10173_hist_splice_cv 31 center_program) + 7 < clock /\
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
      (App «candle_cv_fsa_item_to_q» [from_cv item]) refs =
      (M_success (from_cv program_result),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program»
        [from_cv center_program;from_cv box_program;
         from_cv boxes;from_cv roots]) refs =
    (M_success (from_cv program_result),refs)
Proof
  strip_tac
  >> imp_res_tac
       compute_registeredCase10173ProgramSplicePacketEvalTheory.registered_case10173_prepared_program_splice_length
  >> irule
       compute_registeredCase10173SourceTraceProgramEvalTheory.registered_case10173_source_trace_hist_program_eval
  >> qexists_tac
       `registered_case10173_hist_splice_cv 31 box_program`
  >> qexists_tac `center_boxes`
  >> qexists_tac
       `registered_case10173_hist_splice_cv 31 center_program`
  >> qexists_tac `item`
  >> qexists_tac `item_floor`
  >> qexists_tac `radii`
  >> qexists_tac `stack_tail`
  >> qexists_tac `step_floor`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        compute_registeredCase10173ProgramSpliceEvalTheory.registered_case10173_prepared_program_splice_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        compute_registeredCase10173ProgramSpliceEvalTheory.registered_case10173_prepared_program_splice_eval
      >> asm_rewrite_tac []
      >> intLib.ARITH_TAC)
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
