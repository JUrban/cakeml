(*****************************************************************************
 * Transfer authenticated ordinary source traces to the corrected tag-10
 * equation environment and execute them through the corrected program loop.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10OrdinaryTraceEval
Ancestors
  compute_registeredCase10173Tag10OrdinaryStepEquivalence
  compute_registeredCase10173Tag10HistStepEval
  compute_registeredCase10173Tag10HistProgramRunEval
  compute_registeredCase10173OrdinaryTraceEval
Libs
  bossLib preamble intLib

Definition registered_case10173_tag10_fso_step_eval_above_def:
  registered_case10173_tag10_fso_step_eval_above step_floor
      center_boxes boxes radii center_instruction box_instruction
      stack next_stack <=>
    !clock refs.
      step_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [from_cv center_boxes;from_cv boxes;from_cv radii;
           from_cv center_instruction;from_cv box_instruction;
           from_cv stack]) (refs:hol_refs) =
        (M_success (from_cv next_stack),refs)
End

Definition registered_case10173_tag10_ordinary_program_trace_def:
  (registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii
      (Num center_nil) box_program stack final_stack <=>
        final_stack = stack) /\
  (registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii
      (Pair center_instruction center_program) (Num box_nil)
      stack final_stack <=> final_stack = stack) /\
  (registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii
      (Pair center_instruction center_program)
      (Pair box_instruction box_program) stack final_stack <=>
        center_instruction <> Num 10 /\ box_instruction <> Num 10 /\
        ?next_stack.
          registered_case10173_tag10_fso_step_eval_above step_floor
            center_boxes boxes radii center_instruction box_instruction
            stack next_stack /\
          registered_case10173_tag10_ordinary_program_trace step_floor
            center_boxes boxes radii center_program box_program
            next_stack final_stack)
End

Definition registered_case10173_tag10_supported_program_pair_def:
  (registered_case10173_tag10_supported_program_pair
      (Num center_nil) box_program <=> T) /\
  (registered_case10173_tag10_supported_program_pair
      (Pair center_instruction center_program) (Num box_nil) <=> T) /\
  (registered_case10173_tag10_supported_program_pair
      (Pair center_instruction center_program)
      (Pair box_instruction box_program) <=>
        registered_case10173_tag10_supported_instruction_pair
          center_instruction box_instruction /\
        registered_case10173_tag10_supported_program_pair
          center_program box_program)
End

Theorem registered_case10173_tag10_supported_instruction_not_special:
  registered_case10173_tag10_supported_instruction_pair
      center_instruction box_instruction ==>
  center_instruction <> Num 10 /\ box_instruction <> Num 10
Proof
  strip_tac
  >> fs
       [compute_registeredCase10173Tag10OrdinaryStepEquivalenceTheory.registered_case10173_tag10_supported_instruction_pair_def]
  >> metis_tac []
QED

Theorem registered_case10173_tag10_fso_step_eval_above_from_old:
  1 < step_floor /\
  registered_case10173_tag10_supported_instruction_pair
      center_instruction box_instruction /\
  registered_case10173_fso_step_eval_above step_floor
      center_boxes boxes radii center_instruction box_instruction
      stack next_stack ==>
  registered_case10173_tag10_fso_step_eval_above step_floor
      center_boxes boxes radii center_instruction box_instruction
      stack next_stack
Proof
  rw
    [compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_fso_step_eval_above_def,
     registered_case10173_tag10_fso_step_eval_above_def]
  >> `0 < clock` by intLib.ARITH_TAC
  >> `compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [from_cv center_boxes;from_cv boxes;from_cv radii;
           from_cv center_instruction;from_cv box_instruction;
           from_cv stack]) (refs:hol_refs) =
      compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_fso_program_step_fixed_nonlinear»
          [from_cv center_boxes;from_cv boxes;from_cv radii;
           from_cv center_instruction;from_cv box_instruction;
           from_cv stack]) refs` by
       (irule
          compute_registeredCase10173Tag10OrdinaryStepEquivalenceTheory.registered_case10173_tag10_supported_step_eval_cong
        >> asm_rewrite_tac [])
  >> qpat_x_assum `!clock refs. _`
       (qspecl_then [`clock`,`refs`] mp_tac)
  >> impl_tac >- asm_rewrite_tac []
  >> metis_tac []
QED

Theorem registered_case10173_tag10_ordinary_program_trace_from_old:
  !center_program box_program stack final_stack.
    1 < step_floor /\
    registered_case10173_tag10_supported_program_pair
      center_program box_program /\
    registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii center_program box_program stack final_stack ==>
    registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii center_program box_program stack final_stack
Proof
  Induct_on `center_program`
  >- simp
       [registered_case10173_tag10_supported_program_pair_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def,
        registered_case10173_tag10_ordinary_program_trace_def]
  >> rpt gen_tac
  >> Cases_on `box_program`
  >- simp
       [registered_case10173_tag10_supported_program_pair_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def,
        registered_case10173_tag10_ordinary_program_trace_def]
  >> simp
       [registered_case10173_tag10_supported_program_pair_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def,
        registered_case10173_tag10_ordinary_program_trace_def]
  >> strip_tac
  >> drule
       registered_case10173_tag10_supported_instruction_not_special
  >> strip_tac
  >> asm_rewrite_tac []
  >> qexists_tac `next_stack`
  >> conj_tac
  >- (irule registered_case10173_tag10_fso_step_eval_above_from_old
      >> asm_rewrite_tac [])
  >> first_x_assum match_mp_tac
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_tag10_ordinary_program_trace_sound:
  !center_program box_program stack final_stack clock refs.
    registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii center_program box_program stack final_stack /\
    step_floor + registered_case10173_cv_list_length center_program + 3 <
      clock ==>
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv stack])
      (refs:hol_refs) = (M_success (from_cv final_stack),refs)
Proof
  Induct_on `center_program`
  >- (rpt gen_tac
      >> simp
           [registered_case10173_tag10_ordinary_program_trace_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_center_nil_eval)
      >> intLib.ARITH_TAC)
  >> rpt gen_tac
  >> Cases_on `box_program`
  >- (simp
        [registered_case10173_tag10_ordinary_program_trace_def,
         compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_box_nil_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [registered_case10173_tag10_ordinary_program_trace_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_stack`
  >> conj_tac
  >- (irule
        compute_registeredCase10173Tag10HistStepEvalTheory.registered_case10173_tag10_hist_step_ordinary_eval_from_step
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac >- intLib.ARITH_TAC
      >> fs [registered_case10173_tag10_fso_step_eval_above_def])
  >> first_x_assum match_mp_tac
  >> conj_tac >- asm_rewrite_tac []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
