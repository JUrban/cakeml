(*****************************************************************************
 * The complete 31-instruction genuine case-10173 source prefix.
 *
 * The six authenticated variable/square-root/coefficient/product/term groups
 * are supplied by the checked actual-operand contract.  The initial literal
 * term is supplied by the literal polynomial evaluator.  This theorem joins
 * those numerical facts to the ordinary source-prefix trace without replaying
 * any numerical calculation.
 *****************************************************************************)
Theory compute_registeredCase10173ActualSourcePrefixEval
Ancestors
  compute_registeredCase10173ActualGroupPrefixEval
  compute_boundedCase10173LiteralSourceDecimal
Libs
  bossLib preamble

Theorem registered_case10173_actual_source_prefix_trace:
  LENGTH radii = 6 /\
  LENGTH center_environment = 6 /\
  LENGTH dimensions = 6 /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME center_environment /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
    (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    center_environment
    (Pair center0
      (Pair center1
        (Pair center2
          (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
    (Pair box0
      (Pair box1
        (Pair box2
          (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] ==>
  ?final_stack.
    registered_case10173_ordinary_program_trace 8215
      center_boxes boxes source_radii
      (registered_case10173_source_prefix_template
        center0 center1 center2 center3 center4 center5)
      (registered_case10173_source_prefix_template
        box0 box1 box2 box3 box4 box5)
      stack final_stack
Proof
  strip_tac
  >> `registered_case10173_actual_group_eval_prefix 6 0 center_boxes boxes
        source_radii (registered_case10173_word64_object_cv_list radii)
        (Pair center0
          (Pair center1
            (Pair center2
              (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
        (Pair box0
          (Pair box1
            (Pair box2
              (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
        [certificate0;certificate1;certificate2;
         certificate3;certificate4;certificate5]` by
       (irule registered_case10173_actual_group_eval_prefix_sound
        >> simp []
        >> qexists_tac `dimensions`
        >> asm_rewrite_tac []
        >> qexists_tac `center_environment`
        >> asm_rewrite_tac [])
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_literal_programs_eval_above
  >> qpat_x_assum
       `registered_case10173_actual_group_eval_prefix 6 0 _ boxes _ _ _ _ _`
       mp_tac
  >> simp
       [compute_registeredCase10173ActualGroupPrefixEvalTheory.registered_case10173_actual_group_eval_prefix_compute,
        registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> rpt strip_tac
  >> drule_all_then assume_tac
       compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_authenticated_source_prefix_trace
  >> qpat_x_assum
       `!s. registered_case10173_ordinary_program_trace _ _ _ _ _ _ s _`
       (qspec_then `stack` assume_tac)
  >> fs []
  >> metis_tac []
QED

Theorem registered_case10173_thirteen_result_stack_exists:
  registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes source_radii center_program box_program stack
      (registered_case10173_ordinary_result_stack
        [result12;result11;result10;result9;result8;result7;result6;
         result5;result4;result3;result2;result1;result0] stack) ==>
  ?summands.
    LENGTH summands = 13 /\
    registered_case10173_ordinary_program_trace step_floor
      center_boxes boxes source_radii center_program box_program stack
      (registered_case10173_ordinary_result_stack summands stack)
Proof
  strip_tac
  >> qexists_tac
       `[result12;result11;result10;result9;result8;result7;result6;
         result5;result4;result3;result2;result1;result0]`
  >> simp []
QED

(* Preserve the exact thirteen-result stack shape needed by the ordinary
 * suffix.  The earlier existential final-stack theorem is convenient for
 * standalone prefix clients, but is too weak for the opcode-9/suffix
 * composition because it hides which source results remain below the
 * historical item. *)
Theorem registered_case10173_actual_source_prefix_stack_trace:
  LENGTH radii = 6 /\
  LENGTH center_environment = 6 /\
  LENGTH dimensions = 6 /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME center_environment /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
    (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    center_environment
    (Pair center0
      (Pair center1
        (Pair center2
          (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
    (Pair box0
      (Pair box1
        (Pair box2
          (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] ==>
  ?summands.
    LENGTH summands = 13 /\
    registered_case10173_ordinary_program_trace 8215
      center_boxes boxes source_radii
      (registered_case10173_source_prefix_template
        center0 center1 center2 center3 center4 center5)
      (registered_case10173_source_prefix_template
        box0 box1 box2 box3 box4 box5)
      stack
      (registered_case10173_ordinary_result_stack summands stack)
Proof
  strip_tac
  >> `registered_case10173_actual_group_eval_prefix 6 0 center_boxes boxes
        source_radii (registered_case10173_word64_object_cv_list radii)
        (Pair center0
          (Pair center1
            (Pair center2
              (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
        (Pair box0
          (Pair box1
            (Pair box2
              (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
        [certificate0;certificate1;
         certificate2;certificate3;certificate4;certificate5]` by
       (irule registered_case10173_actual_group_eval_prefix_sound
        >> simp []
        >> qexists_tac `dimensions`
        >> asm_rewrite_tac []
        >> qexists_tac `center_environment`
        >> asm_rewrite_tac [])
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_literal_programs_eval_above
  >> qpat_x_assum
       `registered_case10173_actual_group_eval_prefix 6 0 _ boxes _ _ _ _ _`
       mp_tac
  >> simp
       [compute_registeredCase10173ActualGroupPrefixEvalTheory.registered_case10173_actual_group_eval_prefix_compute,
        registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> rpt strip_tac
  >> drule_all_then assume_tac
       compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_authenticated_source_prefix_trace
  >> qpat_x_assum
       `!s. registered_case10173_ordinary_program_trace _ _ _ _ _ _ s _`
       (qspec_then `stack` assume_tac)
  >> qexists_tac
       `[registered_case10173_constant_object
           registered_case10173_ordinary_term56_value;
         bounded_taylor64_rows_object_cv product'⁵' product_rows'⁵';
         registered_case10173_constant_object
           registered_case10173_ordinary_term56_value;
         bounded_taylor64_rows_object_cv product'⁴' product_rows'⁴';
         registered_case10173_constant_object
           registered_case10173_ordinary_term4_value;
         bounded_taylor64_rows_object_cv product'³' product_rows'³';
         registered_case10173_constant_object
           registered_case10173_ordinary_term23_value;
         bounded_taylor64_rows_object_cv product'' product_rows'';
         registered_case10173_constant_object
           registered_case10173_ordinary_term23_value;
         bounded_taylor64_rows_object_cv product' product_rows';
         registered_case10173_constant_object
           registered_case10173_ordinary_term1_value;
         bounded_taylor64_rows_object_cv product product_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term0_value]`
  >> simp []
  >> qpat_x_assum
       `registered_case10173_ordinary_program_trace (8210 + 5) _ _ _ _ _
          stack (registered_case10173_ordinary_result_stack _ stack)`
       mp_tac
  >> simp []
QED

(* Pin the existential products in the ordinary prefix trace to the products
 * recomputed by the source-shaped bounded checker.  This is the exact stack
 * consumed by the fixed suffix, not merely a thirteen-element shape. *)
Theorem registered_case10173_literal_products_source_prefix_stack_trace:
  LENGTH radii = 6 /\
  LENGTH center_environment = 6 /\
  LENGTH dimensions = 6 /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME center_environment /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
    (bounded_interval64_object_cv_list dimensions) /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    center_environment
    (Pair center0
      (Pair center1
        (Pair center2
          (Pair center3 (Pair center4 (Pair center5 (Num 0)))))))
    (Pair box0
      (Pair box1
        (Pair box2
          (Pair box3 (Pair box4 (Pair box5 (Num 0)))))))
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] /\
  bounded_case10173_literal_products_decimal 6 0 radii center_environment
    [certificate0;certificate1;certificate2;
     certificate3;certificate4;certificate5] =
    SOME [product0;product1;product2;product3;product4;product5] ==>
  ?product0_rows product1_rows product2_rows product3_rows product4_rows
   product5_rows.
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian product0) =
        SOME product0_rows /\
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian product1) =
        SOME product1_rows /\
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian product2) =
        SOME product2_rows /\
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian product3) =
        SOME product3_rows /\
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian product4) =
        SOME product4_rows /\
    bounded_hessian64_rows
      (registered_case10173_taylor_hessian product5) =
        SOME product5_rows /\
    registered_case10173_ordinary_program_trace 8215
      center_boxes boxes source_radii
      (registered_case10173_source_prefix_template
        center0 center1 center2 center3 center4 center5)
      (registered_case10173_source_prefix_template
        box0 box1 box2 box3 box4 box5)
      stack
      (registered_case10173_ordinary_result_stack
        [registered_case10173_constant_object
           registered_case10173_ordinary_term56_value;
         bounded_taylor64_rows_object_cv product5 product5_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term56_value;
         bounded_taylor64_rows_object_cv product4 product4_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term4_value;
         bounded_taylor64_rows_object_cv product3 product3_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term23_value;
         bounded_taylor64_rows_object_cv product2 product2_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term23_value;
         bounded_taylor64_rows_object_cv product1 product1_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term1_value;
         bounded_taylor64_rows_object_cv product0 product0_rows;
         registered_case10173_constant_object
           registered_case10173_ordinary_term0_value]
        stack)
Proof
  strip_tac
  >> Cases_on `certificate0`
  >> Cases_on `certificate1`
  >> Cases_on `certificate2`
  >> Cases_on `certificate3`
  >> Cases_on `certificate4`
  >> Cases_on `certificate5`
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173PolynomialConstantTraceTheory.registered_case10173_literal_programs_eval_above
  >> drule_all_then strip_assume_tac
       (INST_TYPE [alpha |-> ``:cv``]
         (SIMP_RULE std_ss []
           (Q.INST [`remaining:num` |-> `5`, `index:num` |-> `0`]
             registered_case10173_actual_group_numeric_contract)))
  >> pop_assum (qspec_then `boxes:cv` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       (SIMP_RULE std_ss []
         (Q.INST [`remaining:num` |-> `5`, `index:num` |-> `0`]
           compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons))
  >> drule_all_then strip_assume_tac
       (INST_TYPE [alpha |-> ``:cv``]
         (SIMP_RULE std_ss []
           (Q.INST [`remaining:num` |-> `4`, `index:num` |-> `1`]
             registered_case10173_actual_group_numeric_contract)))
  >> pop_assum (qspec_then `boxes:cv` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       (SIMP_RULE std_ss []
         (Q.INST [`remaining:num` |-> `4`, `index:num` |-> `1`]
           compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons))
  >> drule_all_then strip_assume_tac
       (INST_TYPE [alpha |-> ``:cv``]
         (SIMP_RULE std_ss []
           (Q.INST [`remaining:num` |-> `3`, `index:num` |-> `2`]
             registered_case10173_actual_group_numeric_contract)))
  >> pop_assum (qspec_then `boxes:cv` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       (SIMP_RULE std_ss []
         (Q.INST [`remaining:num` |-> `3`, `index:num` |-> `2`]
           compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons))
  >> drule_all_then strip_assume_tac
       (INST_TYPE [alpha |-> ``:cv``]
         (SIMP_RULE std_ss []
           (Q.INST [`remaining:num` |-> `2`, `index:num` |-> `3`]
             registered_case10173_actual_group_numeric_contract)))
  >> pop_assum (qspec_then `boxes:cv` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       (SIMP_RULE std_ss []
         (Q.INST [`remaining:num` |-> `2`, `index:num` |-> `3`]
           compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons))
  >> drule_all_then strip_assume_tac
       (INST_TYPE [alpha |-> ``:cv``]
         (SIMP_RULE std_ss []
           (Q.INST [`remaining:num` |-> `1`, `index:num` |-> `4`]
             registered_case10173_actual_group_numeric_contract)))
  >> pop_assum (qspec_then `boxes:cv` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       (SIMP_RULE std_ss []
         (Q.INST [`remaining:num` |-> `1`, `index:num` |-> `4`]
           compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons))
  >> drule_all_then strip_assume_tac
       (INST_TYPE [alpha |-> ``:cv``]
         (SIMP_RULE std_ss []
           (Q.INST [`remaining:num` |-> `0`, `index:num` |-> `5`]
             registered_case10173_actual_group_numeric_contract)))
  >> pop_assum (qspec_then `boxes:cv` strip_assume_tac)
  >> drule_all_then strip_assume_tac
       (SIMP_RULE std_ss []
         (Q.INST [`remaining:num` |-> `0`, `index:num` |-> `5`]
           compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_cons))
  >> imp_res_tac registered_case10173_constant_taylor_from_checked_constructor
  >> qpat_x_assum
       `bounded_case10173_literal_products_decimal 6 0 _ _ _ = _` mp_tac
  >> fs
       [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_products_decimal_compute,
        registered_case10173_root_coefficients_decimal_at]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> rpt strip_tac
  >> gvs []
  >> irule
       (SIMP_RULE std_ss []
         (Q.INST [`numeric_floor:num` |-> `8210`]
           compute_registeredCase10173OrdinarySourceTemplateEvalTheory.registered_case10173_authenticated_source_prefix_trace))
  >> fs
       [registered_case10173_root_coefficient_programs_def,
        registered_case10173_root_coefficient_values_def,
        registered_case10173_root_term_programs_def,
        registered_case10173_root_term_values_def]
  >> metis_tac []
QED

val _ = export_theory ();
