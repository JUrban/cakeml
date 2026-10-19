(*****************************************************************************
 * Packet-parametric trace for the fixed 15-instruction case-10173 suffix.
 *
 * The suffix evaluates -1, scales the historical Taylor result, and folds
 * the resulting fourteen stack items with thirteen fixed additions.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinarySuffixTraceEval
Ancestors
  compute_registeredCase10173OrdinaryAddChainTraceEval
Libs
  bossLib preamble

Definition registered_case10173_ordinary_negative_one_program_def:
  registered_case10173_ordinary_negative_one_program =
    Pair
      (Pair (Num 0) (Pair (Pair (Num 0) (Num 1)) (Num 0)))
      (Num 0)
End

Definition registered_case10173_ordinary_suffix_instructions_def:
  registered_case10173_ordinary_suffix_instructions summands =
    [Pair (Num 0) registered_case10173_ordinary_negative_one_program;
     Num 4] ++ REPLICATE (LENGTH summands) (Num 3)
End

Definition registered_case10173_ordinary_suffix_numeric_contract_def:
  registered_case10173_ordinary_suffix_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii historical_result summands
      sum_results negative_one_result scaled_result final_result <=>
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;
         from_cv registered_case10173_ordinary_negative_one_program])
      negative_one_result /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_mul»
        [from_cv fixed_radii;from_cv historical_result;
         from_cv negative_one_result])
      scaled_result /\
    registered_case10173_ordinary_add_chain_contract numeric_floor
      fixed_radii summands sum_results scaled_result final_result
End

Theorem registered_case10173_ordinary_suffix_trace:
  registered_case10173_ordinary_suffix_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii historical_result summands
      sum_results negative_one_result scaled_result final_result ==>
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_cv_of_list
        (registered_case10173_ordinary_suffix_instructions summands))
      (registered_case10173_cv_of_list
        (registered_case10173_ordinary_suffix_instructions summands))
      (registered_case10173_ordinary_result_push historical_result
        (registered_case10173_ordinary_result_stack summands stack_tail))
      (registered_case10173_ordinary_result_push final_result stack_tail)
Proof
  rw [registered_case10173_ordinary_suffix_numeric_contract_def]
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii
        (Pair (Num 0) registered_case10173_ordinary_negative_one_program)
        (Pair (Num 0) registered_case10173_ordinary_negative_one_program)
        (registered_case10173_ordinary_result_push historical_result
          (registered_case10173_ordinary_result_stack summands stack_tail))
        (registered_case10173_ordinary_result_push negative_one_result
          (registered_case10173_ordinary_result_push historical_result
            (registered_case10173_ordinary_result_stack summands
              stack_tail)))` by
       (simp
          [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def]
        >> irule compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_fso_poly_step_eval_at_numeric_floor
        >> asm_rewrite_tac [])
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii (Num 4) (Num 4)
        (registered_case10173_ordinary_result_push negative_one_result
          (registered_case10173_ordinary_result_push historical_result
            (registered_case10173_ordinary_result_stack summands
              stack_tail)))
        (registered_case10173_ordinary_result_push scaled_result
          (registered_case10173_ordinary_result_stack summands
            stack_tail))` by
       (simp
          [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def]
        >> irule compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_fso_mul_step_eval_at_numeric_floor
        >> qexists_tac `fixed_radii`
        >> asm_rewrite_tac [])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          [Pair (Num 0) registered_case10173_ordinary_negative_one_program;
           Num 4])
        (registered_case10173_cv_of_list
          [Pair (Num 0) registered_case10173_ordinary_negative_one_program;
           Num 4])
        (registered_case10173_ordinary_result_push historical_result
          (registered_case10173_ordinary_result_stack summands stack_tail))
        (registered_case10173_ordinary_result_push scaled_result
          (registered_case10173_ordinary_result_stack summands
            stack_tail))` by
       (simp
          [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
           compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def]
        >> metis_tac [])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (REPLICATE (LENGTH summands) (Num 3)))
        (registered_case10173_cv_of_list
          (REPLICATE (LENGTH summands) (Num 3)))
        (registered_case10173_ordinary_result_push scaled_result
          (registered_case10173_ordinary_result_stack summands stack_tail))
        (registered_case10173_ordinary_result_push final_result
          stack_tail)` by
       (irule compute_registeredCase10173OrdinaryAddChainTraceEvalTheory.registered_case10173_ordinary_add_chain_trace
        >> qexists_tac `fixed_radii`
        >> qexists_tac `sum_results`
        >> asm_rewrite_tac [])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          ([Pair (Num 0) registered_case10173_ordinary_negative_one_program;
            Num 4] ++ REPLICATE (LENGTH summands) (Num 3)))
        (registered_case10173_cv_of_list
          ([Pair (Num 0) registered_case10173_ordinary_negative_one_program;
            Num 4] ++ REPLICATE (LENGTH summands) (Num 3)))
        (registered_case10173_ordinary_result_push historical_result
          (registered_case10173_ordinary_result_stack summands stack_tail))
        (registered_case10173_ordinary_result_push final_result
          stack_tail)` by
       (irule compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_program_trace_append
        >> conj_tac >- simp []
        >> qexists_tac
             `registered_case10173_ordinary_result_push scaled_result
                (registered_case10173_ordinary_result_stack summands
                  stack_tail)`
        >> asm_rewrite_tac [])
  >> fs [registered_case10173_ordinary_suffix_instructions_def]
QED

Theorem registered_case10173_source_suffix_as_ordinary_suffix:
  LENGTH summands = 13 ==>
  registered_case10173_source_suffix_template =
    registered_case10173_cv_of_list
      (registered_case10173_ordinary_suffix_instructions summands)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_suffix_template_def,
        registered_case10173_ordinary_suffix_instructions_def,
        registered_case10173_ordinary_negative_one_program_def]
  >> fs [listTheory.LENGTH_EQ_NUM_compute]
  >> EVAL_TAC
QED

val _ = export_theory ();
