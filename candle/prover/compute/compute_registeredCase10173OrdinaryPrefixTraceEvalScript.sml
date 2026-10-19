(*****************************************************************************
 * Packet-parametric trace for the 31 ordinary instructions before opcode 9.
 *
 * The prefix is one initial polynomial followed by six coordinate groups.
 * This theory composes the numerical contracts without expanding evaluator
 * semantics or fixing any packet-specific square-root certificates.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryPrefixTraceEval
Ancestors
  compute_registeredCase10173OrdinaryGroupTraceEval
Libs
  bossLib preamble

Definition registered_case10173_ordinary_result_push_def:
  registered_case10173_ordinary_result_push result stack =
    Pair (Pair (Num 1) result) stack
End

Definition registered_case10173_ordinary_group_result_stack_def:
  registered_case10173_ordinary_group_result_stack term_result
      product_result stack =
    registered_case10173_ordinary_result_push term_result
      (registered_case10173_ordinary_result_push product_result stack)
End

Definition registered_case10173_ordinary_prefix_start_def:
  registered_case10173_ordinary_prefix_start initial_program =
    [Pair (Num 0) initial_program]
End

Definition registered_case10173_ordinary_prefix_center_extend_def:
  registered_case10173_ordinary_prefix_center_extend prefix variable_program
      center_certificate coefficient_program term_program =
    prefix ++
      registered_case10173_ordinary_group_center_instructions
        variable_program center_certificate coefficient_program term_program
End

Definition registered_case10173_ordinary_prefix_box_extend_def:
  registered_case10173_ordinary_prefix_box_extend prefix variable_program
      box_certificate coefficient_program term_program =
    prefix ++
      registered_case10173_ordinary_group_box_instructions
        variable_program box_certificate coefficient_program term_program
End

Theorem registered_case10173_ordinary_initial_trace:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv initial_program])
      initial_result ==>
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_cv_of_list
        (registered_case10173_ordinary_prefix_start initial_program))
      (registered_case10173_cv_of_list
        (registered_case10173_ordinary_prefix_start initial_program))
      stack
      (registered_case10173_ordinary_result_push initial_result stack)
Proof
  strip_tac
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii
        (Pair (Num 0) initial_program) (Pair (Num 0) initial_program)
        stack (Pair (Pair (Num 1) initial_result) stack)` by
       (irule compute_registeredCase10173OrdinaryStepAboveEvalTheory.registered_case10173_fso_poly_step_eval_at_numeric_floor
        >> asm_rewrite_tac [])
  >> simp
       [registered_case10173_ordinary_prefix_start_def,
        registered_case10173_ordinary_result_push_def,
        compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def]
QED

Theorem registered_case10173_ordinary_trace_append_group:
  LENGTH center_prefix = LENGTH box_prefix /\
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_cv_of_list center_prefix)
      (registered_case10173_cv_of_list box_prefix)
      stack middle_stack /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program
      center_certificate box_certificate coefficient_program term_program
      variable_result root_result coefficient_result product_result
      term_result ==>
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_cv_of_list
        (registered_case10173_ordinary_prefix_center_extend center_prefix
          variable_program center_certificate coefficient_program
          term_program))
      (registered_case10173_cv_of_list
        (registered_case10173_ordinary_prefix_box_extend box_prefix
          variable_program box_certificate coefficient_program term_program))
      stack
      (registered_case10173_ordinary_group_result_stack term_result
        product_result middle_stack)
Proof
  strip_tac
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_group_center_instructions
            variable_program center_certificate coefficient_program
            term_program))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_group_box_instructions
            variable_program box_certificate coefficient_program
            term_program))
        middle_stack
        (registered_case10173_ordinary_group_result_stack term_result
          product_result middle_stack)` by
       (rw
          [GSYM compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_center_as_instructions,
           GSYM compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_box_as_instructions,
           registered_case10173_ordinary_group_result_stack_def,
           registered_case10173_ordinary_result_push_def]
        >> irule compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_trace_from_contract
        >> metis_tac [])
  >> simp
       [registered_case10173_ordinary_prefix_center_extend_def,
        registered_case10173_ordinary_prefix_box_extend_def]
  >> irule compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_program_trace_append
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `middle_stack`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_ordinary_six_group_prefix_trace:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv initial_program])
      term0 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program0
      center_certificate0 box_certificate0 coefficient_program0
      term_program1 variable_result0 root_result0 coefficient_result0
      product_result0 term1 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program1
      center_certificate1 box_certificate1 coefficient_program1
      term_program2 variable_result1 root_result1 coefficient_result1
      product_result1 term2 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program2
      center_certificate2 box_certificate2 coefficient_program2
      term_program3 variable_result2 root_result2 coefficient_result2
      product_result2 term3 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program3
      center_certificate3 box_certificate3 coefficient_program3
      term_program4 variable_result3 root_result3 coefficient_result3
      product_result3 term4 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program4
      center_certificate4 box_certificate4 coefficient_program4
      term_program5 variable_result4 root_result4 coefficient_result4
      product_result4 term5 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program5
      center_certificate5 box_certificate5 coefficient_program5
      term_program6 variable_result5 root_result5 coefficient_result5
      product_result5 term6 ==>
  let center_prefix0 =
    registered_case10173_ordinary_prefix_start initial_program in
  let box_prefix0 =
    registered_case10173_ordinary_prefix_start initial_program in
  let center_prefix1 = registered_case10173_ordinary_prefix_center_extend
    center_prefix0 variable_program0 center_certificate0 coefficient_program0
    term_program1 in
  let box_prefix1 = registered_case10173_ordinary_prefix_box_extend
    box_prefix0 variable_program0 box_certificate0 coefficient_program0
    term_program1 in
  let center_prefix2 = registered_case10173_ordinary_prefix_center_extend
    center_prefix1 variable_program1 center_certificate1 coefficient_program1
    term_program2 in
  let box_prefix2 = registered_case10173_ordinary_prefix_box_extend
    box_prefix1 variable_program1 box_certificate1 coefficient_program1
    term_program2 in
  let center_prefix3 = registered_case10173_ordinary_prefix_center_extend
    center_prefix2 variable_program2 center_certificate2 coefficient_program2
    term_program3 in
  let box_prefix3 = registered_case10173_ordinary_prefix_box_extend
    box_prefix2 variable_program2 box_certificate2 coefficient_program2
    term_program3 in
  let center_prefix4 = registered_case10173_ordinary_prefix_center_extend
    center_prefix3 variable_program3 center_certificate3 coefficient_program3
    term_program4 in
  let box_prefix4 = registered_case10173_ordinary_prefix_box_extend
    box_prefix3 variable_program3 box_certificate3 coefficient_program3
    term_program4 in
  let center_prefix5 = registered_case10173_ordinary_prefix_center_extend
    center_prefix4 variable_program4 center_certificate4 coefficient_program4
    term_program5 in
  let box_prefix5 = registered_case10173_ordinary_prefix_box_extend
    box_prefix4 variable_program4 box_certificate4 coefficient_program4
    term_program5 in
  let center_prefix6 = registered_case10173_ordinary_prefix_center_extend
    center_prefix5 variable_program5 center_certificate5 coefficient_program5
    term_program6 in
  let box_prefix6 = registered_case10173_ordinary_prefix_box_extend
    box_prefix5 variable_program5 box_certificate5 coefficient_program5
    term_program6 in
  let stack0 = registered_case10173_ordinary_result_push term0 stack in
  let stack1 = registered_case10173_ordinary_group_result_stack
    term1 product_result0 stack0 in
  let stack2 = registered_case10173_ordinary_group_result_stack
    term2 product_result1 stack1 in
  let stack3 = registered_case10173_ordinary_group_result_stack
    term3 product_result2 stack2 in
  let stack4 = registered_case10173_ordinary_group_result_stack
    term4 product_result3 stack3 in
  let stack5 = registered_case10173_ordinary_group_result_stack
    term5 product_result4 stack4 in
  let stack6 = registered_case10173_ordinary_group_result_stack
    term6 product_result5 stack5 in
    registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_cv_of_list center_prefix6)
      (registered_case10173_cv_of_list box_prefix6) stack stack6
Proof
  simp []
  >> strip_tac
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_start initial_program))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_start initial_program))
        stack
        (registered_case10173_ordinary_result_push term0 stack)` by
       (irule registered_case10173_ordinary_initial_trace
        >> asm_rewrite_tac [])
  >> `LENGTH (registered_case10173_ordinary_prefix_start initial_program) =
        LENGTH (registered_case10173_ordinary_prefix_start initial_program)` by
       simp []
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_center_extend
            (registered_case10173_ordinary_prefix_start initial_program)
            variable_program0 center_certificate0 coefficient_program0
            term_program1))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_box_extend
            (registered_case10173_ordinary_prefix_start initial_program)
            variable_program0 box_certificate0 coefficient_program0
            term_program1))
        stack
        (registered_case10173_ordinary_group_result_stack term1
          product_result0
          (registered_case10173_ordinary_result_push term0 stack))` by
       (irule registered_case10173_ordinary_trace_append_group
        >> metis_tac [])
  >> `LENGTH
        (registered_case10173_ordinary_prefix_center_extend
          (registered_case10173_ordinary_prefix_start initial_program)
          variable_program0 center_certificate0 coefficient_program0
          term_program1) =
      LENGTH
        (registered_case10173_ordinary_prefix_box_extend
          (registered_case10173_ordinary_prefix_start initial_program)
          variable_program0 box_certificate0 coefficient_program0
          term_program1)` by
       simp [registered_case10173_ordinary_prefix_center_extend_def,
             registered_case10173_ordinary_prefix_box_extend_def,
             registered_case10173_ordinary_group_center_instructions_def,
             registered_case10173_ordinary_group_box_instructions_def]
  >> qabbrev_tac `center_prefix1 =
       registered_case10173_ordinary_prefix_center_extend
         (registered_case10173_ordinary_prefix_start initial_program)
         variable_program0 center_certificate0 coefficient_program0
         term_program1`
  >> qabbrev_tac `box_prefix1 =
       registered_case10173_ordinary_prefix_box_extend
         (registered_case10173_ordinary_prefix_start initial_program)
         variable_program0 box_certificate0 coefficient_program0
         term_program1`
  >> qabbrev_tac `stack1 =
       registered_case10173_ordinary_group_result_stack term1
         product_result0
         (registered_case10173_ordinary_result_push term0 stack)`
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_center_extend center_prefix1
            variable_program1 center_certificate1 coefficient_program1
            term_program2))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_box_extend box_prefix1
            variable_program1 box_certificate1 coefficient_program1
            term_program2)) stack
        (registered_case10173_ordinary_group_result_stack term2
          product_result1 stack1)` by
       (irule registered_case10173_ordinary_trace_append_group
        >> metis_tac [])
  >> qabbrev_tac `center_prefix2 =
       registered_case10173_ordinary_prefix_center_extend center_prefix1
         variable_program1 center_certificate1 coefficient_program1
         term_program2`
  >> qabbrev_tac `box_prefix2 =
       registered_case10173_ordinary_prefix_box_extend box_prefix1
         variable_program1 box_certificate1 coefficient_program1
         term_program2`
  >> qabbrev_tac `stack2 =
       registered_case10173_ordinary_group_result_stack term2
         product_result1 stack1`
  >> `LENGTH center_prefix2 = LENGTH box_prefix2` by
       (unabbrev_all_tac
        >> simp [registered_case10173_ordinary_prefix_center_extend_def,
                 registered_case10173_ordinary_prefix_box_extend_def,
                 registered_case10173_ordinary_group_center_instructions_def,
                 registered_case10173_ordinary_group_box_instructions_def])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_center_extend center_prefix2
            variable_program2 center_certificate2 coefficient_program2
            term_program3))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_box_extend box_prefix2
            variable_program2 box_certificate2 coefficient_program2
            term_program3)) stack
        (registered_case10173_ordinary_group_result_stack term3
          product_result2 stack2)` by
       (irule registered_case10173_ordinary_trace_append_group
        >> metis_tac [])
  >> qabbrev_tac `center_prefix3 =
       registered_case10173_ordinary_prefix_center_extend center_prefix2
         variable_program2 center_certificate2 coefficient_program2
         term_program3`
  >> qabbrev_tac `box_prefix3 =
       registered_case10173_ordinary_prefix_box_extend box_prefix2
         variable_program2 box_certificate2 coefficient_program2
         term_program3`
  >> qabbrev_tac `stack3 =
       registered_case10173_ordinary_group_result_stack term3
         product_result2 stack2`
  >> `LENGTH center_prefix3 = LENGTH box_prefix3` by
       (unabbrev_all_tac
        >> simp [registered_case10173_ordinary_prefix_center_extend_def,
                 registered_case10173_ordinary_prefix_box_extend_def,
                 registered_case10173_ordinary_group_center_instructions_def,
                 registered_case10173_ordinary_group_box_instructions_def])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_center_extend center_prefix3
            variable_program3 center_certificate3 coefficient_program3
            term_program4))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_box_extend box_prefix3
            variable_program3 box_certificate3 coefficient_program3
            term_program4)) stack
        (registered_case10173_ordinary_group_result_stack term4
          product_result3 stack3)` by
       (irule registered_case10173_ordinary_trace_append_group
        >> metis_tac [])
  >> qabbrev_tac `center_prefix4 =
       registered_case10173_ordinary_prefix_center_extend center_prefix3
         variable_program3 center_certificate3 coefficient_program3
         term_program4`
  >> qabbrev_tac `box_prefix4 =
       registered_case10173_ordinary_prefix_box_extend box_prefix3
         variable_program3 box_certificate3 coefficient_program3
         term_program4`
  >> qabbrev_tac `stack4 =
       registered_case10173_ordinary_group_result_stack term4
         product_result3 stack3`
  >> `LENGTH center_prefix4 = LENGTH box_prefix4` by
       (unabbrev_all_tac
        >> simp [registered_case10173_ordinary_prefix_center_extend_def,
                 registered_case10173_ordinary_prefix_box_extend_def,
                 registered_case10173_ordinary_group_center_instructions_def,
                 registered_case10173_ordinary_group_box_instructions_def])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_center_extend center_prefix4
            variable_program4 center_certificate4 coefficient_program4
            term_program5))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_box_extend box_prefix4
            variable_program4 box_certificate4 coefficient_program4
            term_program5)) stack
        (registered_case10173_ordinary_group_result_stack term5
          product_result4 stack4)` by
       (irule registered_case10173_ordinary_trace_append_group
        >> metis_tac [])
  >> qabbrev_tac `center_prefix5 =
       registered_case10173_ordinary_prefix_center_extend center_prefix4
         variable_program4 center_certificate4 coefficient_program4
         term_program5`
  >> qabbrev_tac `box_prefix5 =
       registered_case10173_ordinary_prefix_box_extend box_prefix4
         variable_program4 box_certificate4 coefficient_program4
         term_program5`
  >> qabbrev_tac `stack5 =
       registered_case10173_ordinary_group_result_stack term5
         product_result4 stack4`
  >> `LENGTH center_prefix5 = LENGTH box_prefix5` by
       (unabbrev_all_tac
        >> simp [registered_case10173_ordinary_prefix_center_extend_def,
                 registered_case10173_ordinary_prefix_box_extend_def,
                 registered_case10173_ordinary_group_center_instructions_def,
                 registered_case10173_ordinary_group_box_instructions_def])
  >> `registered_case10173_ordinary_program_trace (numeric_floor + 5)
        center_boxes boxes radii
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_center_extend center_prefix5
            variable_program5 center_certificate5 coefficient_program5
            term_program6))
        (registered_case10173_cv_of_list
          (registered_case10173_ordinary_prefix_box_extend box_prefix5
            variable_program5 box_certificate5 coefficient_program5
            term_program6)) stack
        (registered_case10173_ordinary_group_result_stack term6
          product_result5 stack5)` by
       (irule registered_case10173_ordinary_trace_append_group
        >> metis_tac [])
  >> unabbrev_all_tac
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
