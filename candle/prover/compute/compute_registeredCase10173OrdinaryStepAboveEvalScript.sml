(*****************************************************************************
 * Clock-uniform constructors for ordinary fixed-nonlinear program steps.
 *
 * The literal case-10173 prefix and suffix should not repeat evaluator clock
 * arithmetic at every instruction.  This layer packages an already proved
 * item calculation as a clock-uniform step relation, ready for composition by
 * the ordinary-program trace theorem.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinaryStepAboveEval
Ancestors
  compute_registeredCase10173OrdinaryTraceEval
Libs
  bossLib preamble intLib

Definition registered_case10173_eval_above_def:
  registered_case10173_eval_above eval_floor expression result <=>
    !clock refs.
      eval_floor < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        expression (refs:hol_refs) = (M_success (from_cv result),refs)
End

Theorem registered_case10173_eval_above_weaken:
  registered_case10173_eval_above lower expression result /\
  lower <= upper ==>
  registered_case10173_eval_above upper expression result
Proof
  rw [registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_step_eval_above_weaken:
  registered_case10173_fso_step_eval_above lower
      center_boxes boxes radii center_instruction box_instruction
      stack next_stack /\
  lower <= upper ==>
  registered_case10173_fso_step_eval_above upper
      center_boxes boxes radii center_instruction box_instruction
      stack next_stack
Proof
  rw
    [compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_fso_step_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_poly_step_eval_above_from_result:
  registered_case10173_eval_above item_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;from_cv center_program]) result ==>
  registered_case10173_fso_step_eval_above (item_floor + 2)
      center_boxes boxes radii
      (Pair (Num 0) center_program) (Pair (Num 0) box_program)
      stack (Pair (Pair (Num 1) result) stack)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_fso_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_poly_eval_from_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> fs [registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_sqrt_step_eval_above_from_item:
  registered_case10173_eval_above item_floor
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;from_cv input]) item ==>
  registered_case10173_fso_step_eval_above (item_floor + 2)
      center_boxes boxes radii
      (Pair (Num 1) center_certificate) (Pair (Num 1) box_certificate)
      (Pair input stack_tail) (Pair item stack_tail)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_fso_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_sqrt_eval_from_item)
  >> conj_tac >- intLib.ARITH_TAC
  >> fs [registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_mul_step_eval_above_from_item:
  registered_case10173_eval_above item_floor
      (App «candle_cv_fso_item_mul»
        [from_cv radii;from_cv left;from_cv right]) item ==>
  registered_case10173_fso_step_eval_above (item_floor + 2)
      center_boxes boxes radii (Num 4) (Num 4)
      (Pair right (Pair left stack_tail)) (Pair item stack_tail)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_fso_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_mul_eval_from_item)
  >> conj_tac >- intLib.ARITH_TAC
  >> fs [registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_add_step_eval_above_from_item:
  registered_case10173_eval_above item_floor
      (App «candle_cv_fsa_item_add»
        [from_cv (Num 1);from_cv radii;from_cv left;from_cv right]) item ==>
  registered_case10173_fso_step_eval_above (item_floor + 2)
      center_boxes boxes radii (Num 3) (Num 3)
      (Pair right (Pair left stack_tail)) (Pair item stack_tail)
Proof
  strip_tac
  >> simp
       [compute_registeredCase10173OrdinaryTraceEvalTheory.registered_case10173_fso_step_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryStepEvalTheory.registered_case10173_fso_program_step_add_eval_from_item)
  >> conj_tac >- intLib.ARITH_TAC
  >> fs [registered_case10173_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fso_item_mul_eval_above_from_result:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_mul»
        [from_cv fixed_radii;from_cv left_result;from_cv right_result])
      result ==>
  registered_case10173_eval_above (numeric_floor + 3)
      (App «candle_cv_fso_item_mul»
        [from_cv radii;
         from_cv (Pair (Num 1) left_result);
         from_cv (Pair (Num 1) right_result)])
      (Pair (Num 1) result)
Proof
  strip_tac
  >> simp [registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryOperationEvalTheory.registered_case10173_fso_item_mul_fixed_eval_from_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `fixed_radii`
  >> conj_tac
  >> fs [registered_case10173_eval_above_def]
QED

Theorem registered_case10173_fsn_item_sqrt_eval_above_from_result:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fsn_result_sqrt»
        [from_cv fixed_radii;from_cv center_certificate;
         from_cv box_certificate;from_cv input_result])
      result ==>
  registered_case10173_eval_above (numeric_floor + 3)
      (App «candle_cv_fsn_item_sqrt»
        [from_cv radii;from_cv center_certificate;
         from_cv box_certificate;
         from_cv (Pair (Num 1) input_result)])
      (Pair (Num 1) result)
Proof
  strip_tac
  >> simp [registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryOperationEvalTheory.registered_case10173_fsn_item_sqrt_fixed_eval_from_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `fixed_radii`
  >> conj_tac
  >> fs [registered_case10173_eval_above_def]
QED

Theorem registered_case10173_fsa_item_add_eval_above_from_result:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_list_of_q» [from_cv radii]) fixed_radii /\
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_result_add»
        [from_cv fixed_radii;from_cv left_result;from_cv right_result])
      result ==>
  registered_case10173_eval_above (numeric_floor + 3)
      (App «candle_cv_fsa_item_add»
        [from_cv (Num 1);from_cv radii;
         from_cv (Pair (Num 1) left_result);
         from_cv (Pair (Num 1) right_result)])
      (Pair (Num 1) result)
Proof
  strip_tac
  >> simp [registered_case10173_eval_above_def]
  >> rpt gen_tac
  >> strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173OrdinaryOperationEvalTheory.registered_case10173_fsa_item_add_fixed_eval_from_result)
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `fixed_radii`
  >> conj_tac
  >> fs [registered_case10173_eval_above_def]
QED

val _ = export_theory ();
