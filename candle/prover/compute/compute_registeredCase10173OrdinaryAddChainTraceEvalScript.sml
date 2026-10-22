(*****************************************************************************
 * A compositional trace theorem for a chain of fixed Taylor-result additions.
 *
 * The case-10173 suffix performs thirteen opcode-3 additions.  This relation
 * keeps the intermediate sums as data and proves the whole repeated program
 * once, instead of constructing thirteen unrelated evaluator arguments.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryAddChainTraceEval
Ancestors
  compute_registeredCase10173OrdinaryPrefixTraceEval
Libs
  bossLib preamble

Definition registered_case10173_ordinary_result_stack_def:
  registered_case10173_ordinary_result_stack [] stack_tail = stack_tail /\
  registered_case10173_ordinary_result_stack (result::results) stack_tail =
    registered_case10173_ordinary_result_push result
      (registered_case10173_ordinary_result_stack results stack_tail)
End

Definition registered_case10173_ordinary_add_chain_contract_def:
  (registered_case10173_ordinary_add_chain_contract numeric_floor fixed_radii
      [] [] accumulator final_result <=> final_result = accumulator) /\
  (registered_case10173_ordinary_add_chain_contract numeric_floor fixed_radii
      [] (sum_result::sum_results) accumulator final_result <=> F) /\
  (registered_case10173_ordinary_add_chain_contract numeric_floor fixed_radii
      (summand::summands) [] accumulator final_result <=> F) /\
  (registered_case10173_ordinary_add_chain_contract numeric_floor fixed_radii
      (summand::summands) (sum_result::sum_results)
      accumulator final_result <=>
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_add»
        [from_cv fixed_radii;from_cv summand;from_cv accumulator])
      sum_result /\
    registered_case10173_ordinary_add_chain_contract numeric_floor
      fixed_radii summands sum_results sum_result final_result)
End

Theorem registered_case10173_ordinary_add_chain_trace:
  !summands sum_results accumulator final_result stack_tail.
    registered_case10173_eval_above numeric_floor
        (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
    registered_case10173_ordinary_add_chain_contract numeric_floor
      fixed_radii summands sum_results accumulator final_result ==>
    registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_cv_of_list
        (REPLICATE (LENGTH summands) (Num 3)))
      (registered_case10173_cv_of_list
        (REPLICATE (LENGTH summands) (Num 3)))
      (registered_case10173_ordinary_result_push accumulator
        (registered_case10173_ordinary_result_stack summands stack_tail))
      (registered_case10173_ordinary_result_push final_result stack_tail)
Proof
  Induct_on `summands`
  >- (rpt gen_tac
      >> Cases_on `sum_results`
      >> simp
           [registered_case10173_ordinary_add_chain_contract_def,
            registered_case10173_ordinary_result_stack_def,
            compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def,
            compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
            compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def])
  >> rpt gen_tac
  >> Cases_on `sum_results`
  >- simp [registered_case10173_ordinary_add_chain_contract_def]
  >> simp [registered_case10173_ordinary_add_chain_contract_def]
  >> strip_tac
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii (Num 3) (Num 3)
        (registered_case10173_ordinary_result_push accumulator
          (registered_case10173_ordinary_result_push h
            (registered_case10173_ordinary_result_stack summands
              stack_tail)))
        (registered_case10173_ordinary_result_push h'
          (registered_case10173_ordinary_result_stack summands
            stack_tail))` by
       (simp
          [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def]
        >> irule compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_fso_add_step_eval_at_numeric_floor
        >> qexists_tac `fixed_radii`
        >> asm_rewrite_tac [])
  >> simp
       [registered_case10173_ordinary_result_stack_def,
        compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def,
        compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def]
  >> qexists_tac
       `registered_case10173_ordinary_result_push h'
          (registered_case10173_ordinary_result_stack summands stack_tail)`
  >> fs
       [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def]
  >> qpat_x_assum
       `!sum_results accumulator' final_result' stack_tail'. _`
       match_mp_tac
  >> qexists_tac `t`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
