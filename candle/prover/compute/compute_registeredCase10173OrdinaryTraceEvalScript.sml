(*****************************************************************************
 * Compositional evaluator semantics for an ordinary paired program trace.
 *
 * Prefix and suffix proofs should describe only the successive stack values;
 * this relation packages a clock-uniform proof for each ordinary source step.
 * The soundness theorem then threads those steps through the registered
 * recursive program runner without invoking the memoized development oracle.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryTraceEval
Ancestors
  compute_registeredCase10173OrdinaryStepEval
  compute_registeredCase10173HistStepEval
Libs
  bossLib preamble intLib

Definition registered_case10173_fso_step_eval_above_def:
  registered_case10173_fso_step_eval_above step_floor
      center_boxes boxes radii center_instruction box_instruction
      stack next_stack <=>
    !clock refs.
      step_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [from_cv center_boxes;from_cv boxes;from_cv radii;
           from_cv center_instruction;from_cv box_instruction;
           from_cv stack]) (refs:hol_refs) =
        (M_success (from_cv next_stack),refs)
End

Definition registered_case10173_ordinary_program_trace_def:
  (registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii
      (Num center_nil) box_program stack final_stack <=>
        final_stack = stack) /\
  (registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii
      (Pair center_instruction center_program) (Num box_nil)
      stack final_stack <=> final_stack = stack) /\
  (registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii
      (Pair center_instruction center_program)
      (Pair box_instruction box_program) stack final_stack <=>
        center_instruction <> Num 9 /\ box_instruction <> Num 9 /\
        ?next_stack.
          registered_case10173_fso_step_eval_above step_floor
            center_boxes boxes radii center_instruction box_instruction
            stack next_stack /\
          registered_case10173_ordinary_program_trace step_floor
            center_boxes boxes radii center_program box_program
            next_stack final_stack)
End

Theorem registered_case10173_ordinary_program_trace_sound:
  !center_program box_program stack final_stack clock refs.
    registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii center_program box_program stack final_stack /\
    step_floor + registered_case10173_cv_list_length center_program + 3 <
      clock ==>
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv stack])
      (refs:hol_refs) = (M_success (from_cv final_stack),refs)
Proof
  Induct_on `center_program`
  >- (rpt gen_tac
      >> simp
           [registered_case10173_ordinary_program_trace_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_center_nil_eval)
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> Cases_on `box_program`
  >- (simp
        [registered_case10173_ordinary_program_trace_def,
         compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_box_nil_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [registered_case10173_ordinary_program_trace_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_stack`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_hist_step_ordinary_eval_from_step
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> fs [registered_case10173_fso_step_eval_above_def]
      )
  >> first_x_assum match_mp_tac
  >> conj_tac >- asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
