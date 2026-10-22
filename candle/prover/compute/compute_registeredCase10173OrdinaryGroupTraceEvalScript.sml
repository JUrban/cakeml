(*****************************************************************************
 * One reusable five-instruction coordinate group in the case-10173 prefix.
 *
 * Each coordinate contributes a polynomial variable, its certified square
 * root, a polynomial coefficient, their product, and the next polynomial
 * source term.  Six instances of this lemma, preceded by the initial source
 * term, make the authenticated 31-instruction prefix.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryGroupTraceEval
Ancestors
  compute_registeredCase10173OrdinaryStepAboveEval
Libs
  bossLib preamble

Definition registered_case10173_ordinary_group_center_def:
  registered_case10173_ordinary_group_center variable_program
      center_certificate coefficient_program term_program =
    registered_case10173_cv_of_list
      [Pair (Num 0) variable_program;
       Pair (Num 1) center_certificate;
       Pair (Num 0) coefficient_program;
       Num 4;
       Pair (Num 0) term_program]
End

Definition registered_case10173_ordinary_group_box_def:
  registered_case10173_ordinary_group_box variable_program
      box_certificate coefficient_program term_program =
    registered_case10173_cv_of_list
      [Pair (Num 0) variable_program;
       Pair (Num 1) box_certificate;
       Pair (Num 0) coefficient_program;
       Num 4;
       Pair (Num 0) term_program]
End

Definition registered_case10173_ordinary_group_center_instructions_def:
  registered_case10173_ordinary_group_center_instructions variable_program
      center_certificate coefficient_program term_program =
    [Pair (Num 0) variable_program;
     Pair (Num 1) center_certificate;
     Pair (Num 0) coefficient_program;
     Num 4;
     Pair (Num 0) term_program]
End

Definition registered_case10173_ordinary_group_box_instructions_def:
  registered_case10173_ordinary_group_box_instructions variable_program
      box_certificate coefficient_program term_program =
    [Pair (Num 0) variable_program;
     Pair (Num 1) box_certificate;
     Pair (Num 0) coefficient_program;
     Num 4;
     Pair (Num 0) term_program]
End

Theorem registered_case10173_ordinary_group_center_as_instructions:
  registered_case10173_ordinary_group_center variable_program
      center_certificate coefficient_program term_program =
    registered_case10173_cv_of_list
      (registered_case10173_ordinary_group_center_instructions
        variable_program center_certificate coefficient_program term_program)
Proof
  rw [registered_case10173_ordinary_group_center_def,
      registered_case10173_ordinary_group_center_instructions_def]
QED

Theorem registered_case10173_ordinary_group_box_as_instructions:
  registered_case10173_ordinary_group_box variable_program
      box_certificate coefficient_program term_program =
    registered_case10173_cv_of_list
      (registered_case10173_ordinary_group_box_instructions
        variable_program box_certificate coefficient_program term_program)
Proof
  rw [registered_case10173_ordinary_group_box_def,
      registered_case10173_ordinary_group_box_instructions_def]
QED

Definition registered_case10173_ordinary_group_numeric_contract_def:
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program center_certificate
      box_certificate coefficient_program term_program variable_result
      root_result coefficient_result product_result term_result <=>
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv variable_program])
      variable_result /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fsn_result_sqrt»
        [from_cv fixed_radii;from_cv center_certificate;
         from_cv box_certificate;from_cv variable_result])
      root_result /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv coefficient_program])
      coefficient_result /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_mul»
        [from_cv fixed_radii;from_cv root_result;
         from_cv coefficient_result])
      product_result /\
    registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv term_program])
      term_result
End

Theorem registered_case10173_ordinary_group_trace:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv variable_program])
      variable_result /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fsn_result_sqrt»
        [from_cv fixed_radii;from_cv center_certificate;
         from_cv box_certificate;from_cv variable_result])
      root_result /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv coefficient_program])
      coefficient_result /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_mul»
        [from_cv fixed_radii;from_cv root_result;
         from_cv coefficient_result])
      product_result /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv term_program])
      term_result ==>
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_ordinary_group_center variable_program
        center_certificate coefficient_program term_program)
      (registered_case10173_ordinary_group_box variable_program
        box_certificate coefficient_program term_program)
      stack
      (Pair (Pair (Num 1) term_result)
        (Pair (Pair (Num 1) product_result) stack))
Proof
  strip_tac
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii
        (Pair (Num 0) variable_program) (Pair (Num 0) variable_program)
        stack (Pair (Pair (Num 1) variable_result) stack)` by
       (irule registered_case10173_fso_poly_step_eval_at_numeric_floor
        >> asm_rewrite_tac [])
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii
        (Pair (Num 1) center_certificate)
        (Pair (Num 1) box_certificate)
        (Pair (Pair (Num 1) variable_result) stack)
        (Pair (Pair (Num 1) root_result) stack)` by
       (irule registered_case10173_fso_sqrt_step_eval_at_numeric_floor
        >> qexists_tac `fixed_radii`
        >> asm_rewrite_tac [])
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii
        (Pair (Num 0) coefficient_program)
        (Pair (Num 0) coefficient_program)
        (Pair (Pair (Num 1) root_result) stack)
        (Pair (Pair (Num 1) coefficient_result)
          (Pair (Pair (Num 1) root_result) stack))` by
       (irule registered_case10173_fso_poly_step_eval_at_numeric_floor
        >> asm_rewrite_tac [])
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii (Num 4) (Num 4)
        (Pair (Pair (Num 1) coefficient_result)
          (Pair (Pair (Num 1) root_result) stack))
        (Pair (Pair (Num 1) product_result) stack)` by
       (irule registered_case10173_fso_mul_step_eval_at_numeric_floor
        >> qexists_tac `fixed_radii`
        >> asm_rewrite_tac [])
  >> `registered_case10173_fso_step_eval_above (numeric_floor + 5)
        center_boxes boxes radii
        (Pair (Num 0) term_program) (Pair (Num 0) term_program)
        (Pair (Pair (Num 1) product_result) stack)
        (Pair (Pair (Num 1) term_result)
          (Pair (Pair (Num 1) product_result) stack))` by
       (irule registered_case10173_fso_poly_step_eval_at_numeric_floor
        >> asm_rewrite_tac [])
  >> simp
       [registered_case10173_ordinary_group_center_def,
        registered_case10173_ordinary_group_box_def,
        compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def]
  >> metis_tac []
QED

Theorem registered_case10173_ordinary_group_trace_from_contract:
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii variable_program center_certificate
      box_certificate coefficient_program term_program variable_result
      root_result coefficient_result product_result term_result ==>
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_ordinary_group_center variable_program
        center_certificate coefficient_program term_program)
      (registered_case10173_ordinary_group_box variable_program
        box_certificate coefficient_program term_program)
      stack
      (Pair (Pair (Num 1) term_result)
        (Pair (Pair (Num 1) product_result) stack))
Proof
  rw [registered_case10173_ordinary_group_numeric_contract_def]
  >> irule registered_case10173_ordinary_group_trace
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `coefficient_result`
  >> qexists_tac `fixed_radii`
  >> qexists_tac `root_result`
  >> qexists_tac `variable_result`
  >> asm_rewrite_tac []
QED

Theorem registered_case10173_ordinary_program_trace_append:
  !center_instructions box_instructions
   center_suffix box_suffix stack middle_stack final_stack.
    LENGTH center_instructions = LENGTH box_instructions /\
    registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii
      (registered_case10173_cv_of_list center_instructions)
      (registered_case10173_cv_of_list box_instructions)
      stack middle_stack /\
    registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii
      (registered_case10173_cv_of_list center_suffix)
      (registered_case10173_cv_of_list box_suffix)
      middle_stack final_stack ==>
    registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes radii
      (registered_case10173_cv_of_list
        (center_instructions ++ center_suffix))
      (registered_case10173_cv_of_list
        (box_instructions ++ box_suffix))
      stack final_stack
Proof
  Induct_on `center_instructions`
  >- simp
       [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def]
  >> rpt gen_tac
  >> Cases_on `box_instructions`
  >- simp []
  >> rpt strip_tac
  >> fs
       [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def,
        compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_ordinary_program_trace_def]
  >> qexists_tac `next_stack`
  >> asm_rewrite_tac []
  >> metis_tac []
QED

val _ = export_theory ();
