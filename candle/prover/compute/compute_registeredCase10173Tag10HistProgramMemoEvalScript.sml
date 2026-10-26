(*****************************************************************************
 * Memoized registered program-run refinement.
 *
 * The historical opcode-10 item is supplied by a previously proved evaluator
 * theorem.  Every other instruction is independently executed by the pure
 * first-order evaluator and refined back to [compute_eval].  This avoids
 * replaying the expensive historical item while preserving the literal
 * registered program-loop semantics.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10HistProgramMemoEval
Ancestors
  compute_registeredCase10173GenuineProgramData
  compute_registeredCase10173HistProgramMemoEval
  compute_registeredCase10173Tag10HistItemCongruence
  compute_registeredCase10173Tag10HistStepEval
  compute_registeredCase10173Tag10HistProgramRunEval
  compute_evalPure
Libs
  bossLib preamble

Definition registered_case10173_hist_item_eval_above_def:
  registered_case10173_hist_item_eval_above item_floor
      center_boxes boxes radii roots item <=>
    !clock refs.
      item_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_item»
          [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots])
        (refs:hol_refs) = (M_success (from_cv item),refs)
End

Definition registered_case10173_hist_program_run_memo_def:
  registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item
      (Num center_nil) box_program stack = SOME stack /\
  registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item
      (Pair center_instruction center_program) (Num box_nil) stack =
        SOME stack /\
  registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item
      (Pair center_instruction center_program)
      (Pair box_instruction box_program) stack =
    if center_instruction = Num 10 then
      if box_instruction = Num 10 then
        registered_case10173_hist_program_run_memo fuel
          center_boxes boxes radii roots item center_program box_program
          (Pair item stack)
      else NONE
    else if box_instruction = Num 10 then NONE
    else
      case
        compute_eval_pure fuel registered_case10173_historical_chunk16_tag10_ceqs
          (App «candle_cv_fso_program_step_fixed_nonlinear»
            [from_cv center_boxes;from_cv boxes;from_cv radii;
             from_cv center_instruction;from_cv box_instruction;
             from_cv stack])
      of
      | NONE => NONE
      | SOME next_stack_expression =>
          case compute_exp_to_cv next_stack_expression of
          | NONE => NONE
          | SOME next_stack =>
              registered_case10173_hist_program_run_memo fuel
                center_boxes boxes radii roots item center_program box_program
                next_stack
End

Theorem registered_case10173_hist_program_run_memo_sound:
  !center_program box_program stack final_stack clock refs.
    registered_case10173_hist_program_run_memo fuel
      center_boxes boxes radii roots item center_program box_program stack =
        SOME final_stack /\
    registered_case10173_hist_item_eval_above item_floor
      center_boxes boxes radii roots item /\
    fuel + item_floor +
      registered_case10173_cv_list_length center_program +
      registered_case10173_cv_list_length box_program + 4 < clock ==>
    compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv center_boxes;from_cv boxes;from_cv radii;from_cv roots;
         from_cv center_program;from_cv box_program;from_cv stack])
      (refs:hol_refs) = (M_success (from_cv final_stack),refs)
Proof
  Induct_on `center_program`
  >- (rpt gen_tac
      >> simp
           [registered_case10173_hist_program_run_memo_def,
            registered_case10173_cv_list_length_def,
            compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_center_nil_eval])
  >> rpt gen_tac
  >> Cases_on `box_program`
  >- (simp
        [registered_case10173_hist_program_run_memo_def,
         registered_case10173_cv_list_length_def,
         compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_box_nil_eval])
  >> Cases_on `center_program = Num 10`
  >> Cases_on `c = Num 10`
  >> fs [registered_case10173_hist_program_run_memo_def]
  >- (strip_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (INST
               [``center_instruction:cv`` |-> ``Num 10:cv``,
                ``box_instruction:cv`` |-> ``Num 10:cv``]
               compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `Pair item stack`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss
              [List.nth
                (CONJUNCTS compute_execTheory.from_cv_def,0)]
              compute_registeredCase10173Tag10HistStepEvalTheory.registered_case10173_tag10_hist_step_special_eval_from_item)
          >> conj_tac >- intLib.ARITH_TAC
          >> fs [registered_case10173_hist_item_eval_above_def]
          >> first_x_assum match_mp_tac
          >> fs [registered_case10173_cv_list_length_def]
          >> intLib.ARITH_TAC)
      >> first_x_assum match_mp_tac
      >> fs [registered_case10173_cv_list_length_def]
      >> intLib.ARITH_TAC)
  >> TOP_CASE_TAC
  >> TOP_CASE_TAC
  >> fs []
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173Tag10HistProgramRunEvalTheory.registered_case10173_tag10_hist_program_run_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `x'`
  >> conj_tac
  >- (irule
        compute_registeredCase10173Tag10HistStepEvalTheory.registered_case10173_tag10_hist_step_ordinary_eval_from_step
      >> conj_tac >- simp []
      >> conj_tac >- simp []
      >> conj_tac >- intLib.ARITH_TAC
      >> drule compute_pureFastTheory.compute_exp_to_cv_sound
      >> strip_tac
      >> fs []
      >> irule compute_evalPureTheory.compute_eval_pure_refines
      >> qexists_tac `fuel`
      >> conj_tac >- intLib.ARITH_TAC
      >> simp [])
  >> first_x_assum match_mp_tac
  >> fs [registered_case10173_cv_list_length_def]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_genuine_hist_item_eval_above:
  ?center_boxes result.
    registered_case10173_q_center_environment_positive
        registered_case10173_first_job_boxes = SOME center_boxes /\
    registered_case10173_hist_item_eval_above 20000 center_boxes
      registered_case10173_first_job_boxes
      (registered_case10173_q_cv_list
        registered_case10173_historical_encoded_radii)
      registered_case10173_first_job_roots (Pair (Num 1) result)
Proof
  mp_tac
    compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_genuine_hist_item_eval_above
  >> simp
       [compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_item_eval_above_def,
        registered_case10173_hist_item_eval_above_def,
        compute_registeredCase10173Tag10HistItemCongruenceTheory.registered_case10173_hist_item_old_tag10_eval_cong]
QED

val _ = export_theory ();
