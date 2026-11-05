(*****************************************************************************
 * Uniform clock-floor interface for every explicit-radius dispatch branch.
 *
 * This is the adapter consumed by the arbitrary-length program trace.  The
 * numerical expression behind a step is supplied once; ordinary/specialized
 * dispatch, source authentication, and state threading are discharged here.
 *****************************************************************************)
Theory compute_boundedCase16594ObjectDispatchStepAboveEval
Ancestors
  compute_boundedCase16594ObjectSpecializedStepControlEval
  compute_boundedCase16594ObjectDispatchStepControlEval
  compute_boundedCase16594ObjectDispatchProgramTraceEval
Libs
  bossLib preamble intLib

Definition bounded_case16594_object_expression_eval_above_def:
  bounded_case16594_object_expression_eval_above eval_floor expression result
      <=>
    !clock refs.
      eval_floor < clock ==>
      compute_eval clock bounded_case16594_object_dispatch_cell0_ceqs
        expression (refs:hol_refs) = (M_success (from_cv result),refs)
End

Theorem bounded_case16594_object_expression_eval_above_weaken:
  bounded_case16594_object_expression_eval_above lower expression result /\
  lower <= upper ==>
  bounded_case16594_object_expression_eval_above upper expression result
Proof
  rw [bounded_case16594_object_expression_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_expression_eval_above_sub:
  bounded_case16594_object_expression_eval_above eval_floor expression result /\
  eval_floor + shift < clock ==>
  compute_eval (clock - shift)
      bounded_case16594_object_dispatch_cell0_ceqs expression (refs:hol_refs) =
    (M_success (from_cv result),refs)
Proof
  rw [bounded_case16594_object_expression_eval_above_def]
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_nonpair_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Num source);from_cv certificates;from_cv stack])
      (Pair (Num 1) (Pair next_stack next_certificates)) ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 0) (Num source)
      certificates stack next_stack next_certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("source",``:cv``) |-> ``(Num (source:num)):cv``]
           bounded_case16594_object_dispatch_ordinary_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_ordinary_nonpair_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_nonzero_pair_eval_above:
  tag <> 0 /\
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_nonpoly_step»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         from_cv (Pair (Num tag) payload);from_cv certificates;from_cv stack])
      (Pair (Num 1) (Pair next_stack next_certificates)) ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 0) (Pair (Num tag) payload)
      certificates stack next_stack next_certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("source",``:cv``) |->
              ``(Pair (Num (tag:num)) (payload:cv)):cv``]
           bounded_case16594_object_dispatch_ordinary_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_ordinary_nonzero_pair_eval)
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_poly_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_poly_run»
        [from_cv center_boxes;from_cv outer_boxes;from_cv radii;
         Uop Snd (from_cv (Pair (Num 0) program));Pair (Num 1) (Num 0)])
      (Pair (Num 1) (Pair result_value (Num 0))) ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 4)
      center_boxes outer_boxes radii (Num 0) (Pair (Num 0) program)
      certificates stack (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("source",``:cv``) |->
              ``(Pair (Num 0) (program:cv)):cv``]
           bounded_case16594_object_dispatch_ordinary_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_ordinary_poly_success_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> first_x_assum match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_product0_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;Num 0])
      result_value ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 1)
      bounded_case16594_object_source35_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("code",``:num``) |-> ``1:num``,
            mk_var("source",``:cv``) |->
              ``bounded_case16594_object_source35_cv``]
           bounded_case16594_object_dispatch_specialized_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_specialized_product0_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!eval_clock eval_refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_product1_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;Num 1])
      result_value ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 2)
      bounded_case16594_object_source78_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("code",``:num``) |-> ``2:num``,
            mk_var("source",``:cv``) |->
              ``bounded_case16594_object_source78_cv``]
           bounded_case16594_object_dispatch_specialized_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_specialized_product1_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!eval_clock eval_refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_product2_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_delta_product_source_item_state»
        [from_cv radii;from_cv center_boxes;from_cv outer_boxes;Num 2])
      result_value ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 3)
      bounded_case16594_object_source121_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("code",``:num``) |-> ``3:num``,
            mk_var("source",``:cv``) |->
              ``bounded_case16594_object_source121_cv``]
           bounded_case16594_object_dispatch_specialized_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_specialized_product2_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!eval_clock eval_refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_neg3_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;Num 3]) result_value ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 4)
      bounded_case16594_object_source34_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("code",``:num``) |-> ``4:num``,
            mk_var("source",``:cv``) |->
              ``bounded_case16594_object_source34_cv``]
           bounded_case16594_object_dispatch_specialized_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_specialized_neg3_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!eval_clock eval_refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_neg4_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;Num 4]) result_value ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 5)
      bounded_case16594_object_source77_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("code",``:num``) |-> ``5:num``,
            mk_var("source",``:cv``) |->
              ``bounded_case16594_object_source77_cv``]
           bounded_case16594_object_dispatch_specialized_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_specialized_neg4_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!eval_clock eval_refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

Theorem bounded_case16594_object_dispatch_neg5_eval_above:
  bounded_case16594_object_expression_eval_above numeric_floor
      (App «candle_cv_q_packed_object_delta_neg_derivative_item_state»
        [from_cv radii;from_cv center_boxes;Num 5]) result_value ==>
  bounded_case16594_object_dispatch_step_eval_above (numeric_floor + 2)
      center_boxes outer_boxes radii (Num 6)
      bounded_case16594_object_source120_cv certificates stack
      (Pair result_value stack) certificates
Proof
  rw [bounded_case16594_object_expression_eval_above_def,
      bounded_case16594_object_dispatch_step_eval_above_def]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         (INST
           [mk_var("code",``:num``) |-> ``6:num``,
            mk_var("source",``:cv``) |->
              ``bounded_case16594_object_source120_cv``]
           bounded_case16594_object_dispatch_specialized_eval))
  >> conj_tac >- intLib.ARITH_TAC
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         bounded_case16594_object_specialized_neg5_eval)
  >> conj_tac >- intLib.ARITH_TAC
  >> qpat_x_assum `!eval_clock eval_refs. _` match_mp_tac
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
