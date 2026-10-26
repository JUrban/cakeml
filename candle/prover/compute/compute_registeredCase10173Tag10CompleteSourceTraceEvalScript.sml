Theory compute_registeredCase10173Tag10CompleteSourceTraceEval
Ancestors
  compute_registeredCase10173OrdinarySourceTemplateEval
  compute_registeredCase10173Tag10OrdinaryTraceEval
  compute_registeredCase10173Tag10HistProgramMemoEval
Libs
  bossLib preamble intLib

Definition registered_case10173_tag10_hist_item_eval_above_def:
  registered_case10173_tag10_hist_item_eval_above item_floor
      center_boxes boxes radii roots item <=>
    !clock refs.
      item_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_item»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
        (refs:hol_refs) = (M_success (from_cv item),refs)
End

Definition registered_case10173_tag10_source_program_trace_def:
  (registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item
      (Num center_nil) box_program stack final_stack <=>
        final_stack = stack) /\
  (registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item
      (Pair center_instruction center_program) (Num box_nil)
      stack final_stack <=> final_stack = stack) /\
  (registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item
      (Pair center_instruction center_program)
      (Pair box_instruction box_program) stack final_stack <=>
        if center_instruction = Num 10 then
          box_instruction = Num 10 /\
          registered_case10173_tag10_hist_item_eval_above item_floor
            center_boxes boxes radii roots item /\
          registered_case10173_tag10_source_program_trace step_floor item_floor
            center_boxes boxes radii roots item center_program box_program
            (Pair item stack) final_stack
        else
          box_instruction <> Num 10 /\
          ?next_stack.
            registered_case10173_tag10_fso_step_eval_above step_floor
              center_boxes boxes radii center_instruction box_instruction
              stack next_stack /\
            registered_case10173_tag10_source_program_trace step_floor item_floor
              center_boxes boxes radii roots item center_program box_program
              next_stack final_stack)
End

Theorem registered_case10173_tag10_source_program_trace_sound:
  !center_program box_program stack final_stack clock refs.
    registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item center_program box_program
      stack final_stack /\
    step_floor + item_floor +
      registered_case10173_cv_list_length center_program + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv stack])
      (refs:hol_refs) = (M_success (from_cv final_stack),refs)
Proof
  Induct_on `center_program`
  >- (rpt gen_tac
      >> simp
           [registered_case10173_tag10_source_program_trace_def,
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
        [registered_case10173_tag10_source_program_trace_def,
         compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
      >> strip_tac
      >> qpat_x_assum `final_stack = stack` kall_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_box_nil_eval)
      >> intLib.ARITH_TAC)
  >> simp
       [registered_case10173_tag10_source_program_trace_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> Cases_on `center_program = Num 10`
  >- (simp []
      >> strip_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (Q.INST
               [`center_instruction:cv` |-> `Num 10`,
                `box_instruction:cv` |-> `Num 10`,
                `center_program:cv` |-> `center_program'`,
                `box_program:cv` |-> `c0`]
               compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `Pair item stack`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss
              [List.nth (CONJUNCTS compute_execTheory.from_cv_def,0)]
              compute_registeredCase10173Tag10HistStepEvalTheory.registered_case10173_tag10_hist_step_special_eval_from_item)
          >> conj_tac >- intLib.ARITH_TAC
          >> qpat_x_assum
               `registered_case10173_tag10_hist_item_eval_above item_floor
                  center_boxes boxes radii roots item` mp_tac
          >> rw
               [registered_case10173_tag10_hist_item_eval_above_def]
          >> first_x_assum match_mp_tac
          >> intLib.ARITH_TAC)
      >> qpat_x_assum
           `!box_program stack final_stack clock refs.
              registered_case10173_tag10_source_program_trace step_floor
                item_floor center_boxes boxes radii roots item
                center_program' box_program stack final_stack /\ _ ==> _`
           (qspecl_then
             [`c0`,`Pair item stack`,`final_stack`,`clock - 1`,`refs`]
             mp_tac)
      >> impl_tac
      >- (conj_tac >- asm_rewrite_tac []
          >> intLib.ARITH_TAC)
      >> simp [])
  >> simp []
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (Q.INST
           [`center_instruction:cv` |-> `center_program`,
            `box_instruction:cv` |-> `c`,
            `center_program:cv` |-> `center_program'`,
            `box_program:cv` |-> `c0`]
           compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_cons_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `next_stack`
  >> conj_tac
  >- (irule
        compute_registeredCase10173Tag10HistStepEvalTheory.registered_case10173_tag10_hist_step_ordinary_eval_from_step
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac >- asm_rewrite_tac []
      >> conj_tac
      >- (qpat_x_assum
            `item_floor +
               (step_floor +
                (SUC
                   (registered_case10173_cv_list_length
                     center_program') + 4)) < clock` mp_tac
          >> rpt (pop_assum kall_tac)
          >> intLib.ARITH_TAC)
      >> qpat_x_assum
           `registered_case10173_tag10_fso_step_eval_above step_floor
              center_boxes boxes radii center_program c stack next_stack`
           (fn th =>
              mp_tac
                (Q.SPECL [`clock - 2`,`refs`]
                  (REWRITE_RULE
                    [compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_fso_step_eval_above_def]
                    th)))
      >> impl_tac
      >- (qpat_x_assum
            `item_floor +
               (step_floor +
                (SUC
                   (registered_case10173_cv_list_length
                     center_program') + 4)) < clock` mp_tac
          >> rpt (pop_assum kall_tac)
          >> intLib.ARITH_TAC)
      >> simp [])
  >> qpat_x_assum
       `!box_program stack final_stack clock refs.
          registered_case10173_tag10_source_program_trace step_floor item_floor
            center_boxes boxes radii roots item center_program' box_program
            stack final_stack /\ _ ==> _`
       (qspecl_then
         [`c0`,`next_stack`,`final_stack`,`clock - 1`,`refs`] mp_tac)
  >> impl_tac
  >- (conj_tac >- asm_rewrite_tac []
      >> qpat_x_assum
           `item_floor +
              (step_floor +
               (SUC
                  (registered_case10173_cv_list_length center_program') +
                4)) < clock` mp_tac
      >> rpt (pop_assum kall_tac)
      >> intLib.ARITH_TAC)
  >> simp []
QED

Theorem registered_case10173_tag10_ordinary_trace_is_source_trace:
  !center_program box_program stack final_stack.
    registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii center_program box_program stack final_stack ==>
    registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item center_program box_program
      stack final_stack
Proof
  Induct_on `center_program`
  >- simp
       [compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_def,
        registered_case10173_tag10_source_program_trace_def]
  >> rpt gen_tac
  >> Cases_on `box_program`
  >- simp
       [compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_def,
        registered_case10173_tag10_source_program_trace_def]
  >> simp
       [compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_def,
        registered_case10173_tag10_source_program_trace_def]
  >> metis_tac []
QED

Theorem registered_case10173_tag10_source_trace_append_ordinary_prefix:
  !center_prefix box_prefix stack middle_stack final_stack.
    registered_case10173_cv_list_length center_prefix =
      registered_case10173_cv_list_length box_prefix /\
    registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii center_prefix box_prefix stack middle_stack /\
    registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item center_suffix box_suffix
      middle_stack final_stack ==>
    registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item
      (registered_case10173_cv_append center_prefix center_suffix)
      (registered_case10173_cv_append box_prefix box_suffix)
      stack final_stack
Proof
  Induct_on `center_prefix`
  >- (rpt gen_tac
      >> Cases_on `box_prefix`
      >> simp
           [compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
            compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_def]
      >> metis_tac [])
  >> rpt gen_tac
  >> Cases_on `box_prefix`
  >- simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> simp
       [compute_registeredCase10173ProgramSplitPacketEvalTheory.registered_case10173_cv_append_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
        compute_registeredCase10173Tag10OrdinaryTraceEvalTheory.registered_case10173_tag10_ordinary_program_trace_def,
        registered_case10173_tag10_source_program_trace_def]
  >> metis_tac []
QED

Theorem registered_case10173_tag10_prefix_item_suffix_source_trace:
  registered_case10173_cv_list_length center_prefix =
      registered_case10173_cv_list_length box_prefix /\
  registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii center_prefix box_prefix stack prefix_stack /\
  registered_case10173_tag10_hist_item_eval_above item_floor
      center_boxes boxes radii roots item /\
  registered_case10173_tag10_ordinary_program_trace step_floor
      center_boxes boxes radii center_suffix box_suffix
      (Pair item prefix_stack) final_stack ==>
  registered_case10173_tag10_source_program_trace step_floor item_floor
      center_boxes boxes radii roots item
      (registered_case10173_cv_append center_prefix
        (Pair (Num 10) center_suffix))
      (registered_case10173_cv_append box_prefix
        (Pair (Num 10) box_suffix))
      stack final_stack
Proof
  strip_tac
  >> irule registered_case10173_tag10_source_trace_append_ordinary_prefix
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `prefix_stack`
  >> conj_tac >- asm_rewrite_tac []
  >> simp [registered_case10173_tag10_source_program_trace_def]
  >> irule registered_case10173_tag10_ordinary_trace_is_source_trace
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
