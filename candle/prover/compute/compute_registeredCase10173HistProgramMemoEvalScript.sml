(*****************************************************************************
 * Memoized registered program-run refinement.
 *
 * The historical opcode-9 item is supplied by a previously proved evaluator
 * theorem.  Every other instruction is independently executed by the pure
 * first-order evaluator and refined back to [compute_eval].  This avoids
 * replaying the expensive historical item while preserving the literal
 * registered program-loop semantics.
 *****************************************************************************)
Theory compute_registeredCase10173HistProgramMemoEval
Ancestors
  compute_registeredCase10173GenuineProgramData
  compute_evalPure
Libs
  bossLib preamble

Definition registered_case10173_hist_item_eval_above_def:
  registered_case10173_hist_item_eval_above item_floor
      center_boxes boxes radii roots item <=>
    !clock refs.
      item_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
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
    if center_instruction = Num 9 then
      if box_instruction = Num 9 then
        registered_case10173_hist_program_run_memo fuel
          center_boxes boxes radii roots item center_program box_program
          (Pair item stack)
      else NONE
    else if box_instruction = Num 9 then NONE
    else
      case
        compute_eval_pure fuel registered_case10173_historical_chunk16_ceqs
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
    compute_eval clock registered_case10173_historical_chunk16_ceqs
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
            compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_center_nil_eval])
  >> rpt gen_tac
  >> Cases_on `box_program`
  >- (simp
        [registered_case10173_hist_program_run_memo_def,
         registered_case10173_cv_list_length_def,
         compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_box_nil_eval])
  >> Cases_on `center_program = Num 9`
  >> Cases_on `c = Num 9`
  >> fs [registered_case10173_hist_program_run_memo_def]
  >- (strip_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             (INST
               [``center_instruction:cv`` |-> ``Num 9:cv``,
                ``box_instruction:cv`` |-> ``Num 9:cv``]
               compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_cons_eval))
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `Pair item stack`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss
              [List.nth
                (CONJUNCTS compute_execTheory.from_cv_def,0)]
              compute_registeredCase10173HistStepEvalTheory.registered_case10173_hist_step_special_eval_from_item)
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
         compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_hist_program_run_cons_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `x'`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_hist_step_ordinary_eval_from_step
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
    compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_source_inputs_exact
  >> strip_tac
  >> mp_tac
    compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_historical_item_complete
  >> strip_tac
  >> qexists_tac `center_boxes`
  >> qexists_tac `result`
  >> conj_tac >- simp []
  >> PURE_REWRITE_TAC [registered_case10173_hist_item_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> qpat_x_assum
       `registered_case10173_first_job_roots = _`
       (fn th => once_rewrite_tac [th])
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> irule
       compute_registeredCase10173HistItemCompleteObjectEvalTheory.registered_case10173_hist_item_complete_object_eval
  >> `LENGTH center_gradient = 6` by
       (irule
          compute_registeredCase10173GenuineHistItemCallEvalTheory.registered_case10173_historical_center_gradient_length
        >> simp [])
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (simp
        [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_def,
         compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >> qexists_tac
       `registered_case10173_historical_box_environment_decimal`
  >> qexists_tac `box_gradient`
  >> qexists_tac `box_value`
  >> qexists_tac
       `registered_case10173_historical_center_environment_decimal`
  >> qexists_tac `center_gradient`
  >> qexists_tac `center_value`
  >> qexists_tac `hessian`
  >> qexists_tac `registered_case10173_historical_radii_words`
  >> qexists_tac `rows`
  >> rpt conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_decimal_def,
         compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- simp []
  >- (simp
        [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
         compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- simp []
  >- (simp
        [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- ACCEPT_TAC
       compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_numerators
  >- simp []
  >- simp []
  >- (once_rewrite_tac
        [GSYM
          compute_registeredCase10173GenuineHistItemCallEvalTheory.registered_case10173_historical_center_environment_object_exact]
      >> mp_tac
           (Q.INST [`clock` |-> `clock - 3`]
             compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_first_order_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> qpat_x_assum
           `bounded_historical_dihedral_first64_decimal _ _ _
              registered_case10173_historical_center_reciprocals = _`
           (fn th =>
             assume_tac
               (REWRITE_RULE
                 [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_reciprocals_components]
                 th))
      >> gvs [])
  >> once_rewrite_tac
       [GSYM compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_object_exact]
  >> irule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_second_order_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
