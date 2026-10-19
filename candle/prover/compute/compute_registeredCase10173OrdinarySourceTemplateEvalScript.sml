(*****************************************************************************
 * Named polynomial programs and six-group decomposition of the authenticated
 * case-10173 source prefix.  These names connect the generic prefix trace to
 * the exact source bytes without duplicating evaluator semantics.
 *****************************************************************************)
Theory compute_registeredCase10173OrdinarySourceTemplateEval
Ancestors
  compute_registeredCase10173OrdinarySuffixTraceEval
Libs
  bossLib preamble

Definition registered_case10173_ordinary_variable_program_def:
  registered_case10173_ordinary_variable_program index =
    Pair (Pair (Num 1) (Num index)) (Num 0)
End

Definition registered_case10173_ordinary_term0_program_def:
  registered_case10173_ordinary_term0_program =
    Pair
      (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
      (Pair
        (Pair (Num 0) (Pair (Pair (Num 1277) (Num 0)) (Num 999)))
        (Pair (Num 4) (Num 0)))
End

Definition registered_case10173_ordinary_coefficient0_program_def:
  registered_case10173_ordinary_coefficient0_program =
    Pair
      (Pair (Num 0)
        (Pair (Pair (Num 136649) (Num 0)) (Num 499999)))
      (Num 0)
End

Definition registered_case10173_ordinary_term1_program_def:
  registered_case10173_ordinary_term1_program =
    Pair
      (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
      (Pair
        (Pair (Num 0)
          (Pair (Pair (Num 136649) (Num 0)) (Num 499999)))
        (Pair
          (Pair (Num 0) (Pair (Pair (Num 109) (Num 0)) (Num 49)))
          (Pair (Num 2) (Pair (Num 4) (Pair (Num 4) (Num 0))))))
End

Definition registered_case10173_ordinary_coefficient12_program_def:
  registered_case10173_ordinary_coefficient12_program =
    Pair
      (Pair (Num 0)
        (Pair (Pair (Num 273853) (Num 0)) (Num 999999)))
      (Pair (Num 2) (Num 0))
End

Definition registered_case10173_ordinary_term23_program_def:
  registered_case10173_ordinary_term23_program =
    Pair
      (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
      (Pair
        (Pair (Num 0)
          (Pair (Pair (Num 273853) (Num 0)) (Num 999999)))
        (Pair
          (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
          (Pair (Num 4) (Pair (Num 4) (Num 0)))))
End

Definition registered_case10173_ordinary_coefficient3_program_def:
  registered_case10173_ordinary_coefficient3_program =
    Pair
      (Pair (Num 0)
        (Pair (Pair (Num 354409) (Num 0)) (Num 499999)))
      (Num 0)
End

Definition registered_case10173_ordinary_term4_program_def:
  registered_case10173_ordinary_term4_program =
    Pair
      (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
      (Pair
        (Pair (Num 0)
          (Pair (Pair (Num 354409) (Num 0)) (Num 499999)))
        (Pair
          (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
          (Pair (Num 2)
            (Pair (Num 4) (Pair (Num 4) (Num 0))))))
End

Definition registered_case10173_ordinary_coefficient45_program_def:
  registered_case10173_ordinary_coefficient45_program =
    Pair
      (Pair (Num 0)
        (Pair (Pair (Num 78497) (Num 0)) (Num 249999)))
      (Pair (Num 2) (Num 0))
End

Definition registered_case10173_ordinary_term56_program_def:
  registered_case10173_ordinary_term56_program =
    Pair
      (Pair (Num 0) (Pair (Pair (Num 1) (Num 0)) (Num 0)))
      (Pair
        (Pair (Num 0)
          (Pair (Pair (Num 78497) (Num 0)) (Num 249999)))
        (Pair
          (Pair (Num 0) (Pair (Pair (Num 2) (Num 0)) (Num 0)))
          (Pair (Num 4) (Pair (Num 4) (Num 0)))))
End

Definition registered_case10173_ordinary_source_prefix_center_def:
  registered_case10173_ordinary_source_prefix_center
      center0 center1 center2 center3 center4 center5 =
    registered_case10173_ordinary_prefix_center_extend
      (registered_case10173_ordinary_prefix_center_extend
        (registered_case10173_ordinary_prefix_center_extend
          (registered_case10173_ordinary_prefix_center_extend
            (registered_case10173_ordinary_prefix_center_extend
              (registered_case10173_ordinary_prefix_center_extend
                (registered_case10173_ordinary_prefix_start
                  registered_case10173_ordinary_term0_program)
                (registered_case10173_ordinary_variable_program 0)
                center0 registered_case10173_ordinary_coefficient0_program
                registered_case10173_ordinary_term1_program)
              (registered_case10173_ordinary_variable_program 1)
              center1 registered_case10173_ordinary_coefficient12_program
              registered_case10173_ordinary_term23_program)
            (registered_case10173_ordinary_variable_program 2)
            center2 registered_case10173_ordinary_coefficient12_program
            registered_case10173_ordinary_term23_program)
          (registered_case10173_ordinary_variable_program 3)
          center3 registered_case10173_ordinary_coefficient3_program
          registered_case10173_ordinary_term4_program)
        (registered_case10173_ordinary_variable_program 4)
        center4 registered_case10173_ordinary_coefficient45_program
        registered_case10173_ordinary_term56_program)
      (registered_case10173_ordinary_variable_program 5)
      center5 registered_case10173_ordinary_coefficient45_program
      registered_case10173_ordinary_term56_program
End

Definition registered_case10173_ordinary_source_prefix_box_def:
  registered_case10173_ordinary_source_prefix_box
      box0 box1 box2 box3 box4 box5 =
    registered_case10173_ordinary_prefix_box_extend
      (registered_case10173_ordinary_prefix_box_extend
        (registered_case10173_ordinary_prefix_box_extend
          (registered_case10173_ordinary_prefix_box_extend
            (registered_case10173_ordinary_prefix_box_extend
              (registered_case10173_ordinary_prefix_box_extend
                (registered_case10173_ordinary_prefix_start
                  registered_case10173_ordinary_term0_program)
                (registered_case10173_ordinary_variable_program 0)
                box0 registered_case10173_ordinary_coefficient0_program
                registered_case10173_ordinary_term1_program)
              (registered_case10173_ordinary_variable_program 1)
              box1 registered_case10173_ordinary_coefficient12_program
              registered_case10173_ordinary_term23_program)
            (registered_case10173_ordinary_variable_program 2)
            box2 registered_case10173_ordinary_coefficient12_program
            registered_case10173_ordinary_term23_program)
          (registered_case10173_ordinary_variable_program 3)
          box3 registered_case10173_ordinary_coefficient3_program
          registered_case10173_ordinary_term4_program)
        (registered_case10173_ordinary_variable_program 4)
        box4 registered_case10173_ordinary_coefficient45_program
        registered_case10173_ordinary_term56_program)
      (registered_case10173_ordinary_variable_program 5)
      box5 registered_case10173_ordinary_coefficient45_program
      registered_case10173_ordinary_term56_program
End

Theorem registered_case10173_source_prefix_as_ordinary_center:
  registered_case10173_source_prefix_template
      center0 center1 center2 center3 center4 center5 =
    registered_case10173_cv_of_list
      (registered_case10173_ordinary_source_prefix_center
        center0 center1 center2 center3 center4 center5)
Proof
  simp
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_prefix_template_def,
     registered_case10173_ordinary_source_prefix_center_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_start_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_center_extend_def,
     compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_center_instructions_def,
     registered_case10173_ordinary_variable_program_def,
     registered_case10173_ordinary_term0_program_def,
     registered_case10173_ordinary_coefficient0_program_def,
     registered_case10173_ordinary_term1_program_def,
     registered_case10173_ordinary_coefficient12_program_def,
     registered_case10173_ordinary_term23_program_def,
     registered_case10173_ordinary_coefficient3_program_def,
     registered_case10173_ordinary_term4_program_def,
     registered_case10173_ordinary_coefficient45_program_def,
     registered_case10173_ordinary_term56_program_def]
QED

Theorem registered_case10173_source_prefix_as_ordinary_box:
  registered_case10173_source_prefix_template
      box0 box1 box2 box3 box4 box5 =
    registered_case10173_cv_of_list
      (registered_case10173_ordinary_source_prefix_box
        box0 box1 box2 box3 box4 box5)
Proof
  simp
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_prefix_template_def,
     registered_case10173_ordinary_source_prefix_box_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_start_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_box_extend_def,
     compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_box_instructions_def,
     registered_case10173_ordinary_variable_program_def,
     registered_case10173_ordinary_term0_program_def,
     registered_case10173_ordinary_coefficient0_program_def,
     registered_case10173_ordinary_term1_program_def,
     registered_case10173_ordinary_coefficient12_program_def,
     registered_case10173_ordinary_term23_program_def,
     registered_case10173_ordinary_coefficient3_program_def,
     registered_case10173_ordinary_term4_program_def,
     registered_case10173_ordinary_coefficient45_program_def,
     registered_case10173_ordinary_term56_program_def]
QED

Theorem registered_case10173_ordinary_source_prefix_lengths:
  LENGTH
    (registered_case10173_ordinary_source_prefix_center
      center0 center1 center2 center3 center4 center5) = 31 /\
  LENGTH
    (registered_case10173_ordinary_source_prefix_box
      box0 box1 box2 box3 box4 box5) = 31
Proof
  simp
    [registered_case10173_ordinary_source_prefix_center_def,
     registered_case10173_ordinary_source_prefix_box_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_start_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_center_extend_def,
     compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_prefix_box_extend_def,
     compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_center_instructions_def,
     compute_registeredCase10173OrdinaryGroupTraceEvalTheory.registered_case10173_ordinary_group_box_instructions_def]
QED

Theorem registered_case10173_authenticated_source_prefix_trace:
  registered_case10173_eval_above numeric_floor
      (App «candle_cv_fs_poly_program»
        [from_cv center_boxes;from_cv radii;
         from_cv registered_case10173_ordinary_term0_program])
      term0 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii
      (registered_case10173_ordinary_variable_program 0)
      center0 box0 registered_case10173_ordinary_coefficient0_program
      registered_case10173_ordinary_term1_program
      variable_result0 root_result0 coefficient_result0 product_result0
      term1 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii
      (registered_case10173_ordinary_variable_program 1)
      center1 box1 registered_case10173_ordinary_coefficient12_program
      registered_case10173_ordinary_term23_program
      variable_result1 root_result1 coefficient_result1 product_result1
      term2 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii
      (registered_case10173_ordinary_variable_program 2)
      center2 box2 registered_case10173_ordinary_coefficient12_program
      registered_case10173_ordinary_term23_program
      variable_result2 root_result2 coefficient_result2 product_result2
      term3 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii
      (registered_case10173_ordinary_variable_program 3)
      center3 box3 registered_case10173_ordinary_coefficient3_program
      registered_case10173_ordinary_term4_program
      variable_result3 root_result3 coefficient_result3 product_result3
      term4 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii
      (registered_case10173_ordinary_variable_program 4)
      center4 box4 registered_case10173_ordinary_coefficient45_program
      registered_case10173_ordinary_term56_program
      variable_result4 root_result4 coefficient_result4 product_result4
      term5 /\
  registered_case10173_ordinary_group_numeric_contract numeric_floor
      center_boxes boxes radii fixed_radii
      (registered_case10173_ordinary_variable_program 5)
      center5 box5 registered_case10173_ordinary_coefficient45_program
      registered_case10173_ordinary_term56_program
      variable_result5 root_result5 coefficient_result5 product_result5
      term6 ==>
  registered_case10173_ordinary_program_trace (numeric_floor + 5)
      center_boxes boxes radii
      (registered_case10173_source_prefix_template
        center0 center1 center2 center3 center4 center5)
      (registered_case10173_source_prefix_template
        box0 box1 box2 box3 box4 box5)
      stack
      (registered_case10173_ordinary_result_stack
        [term6;product_result5;term5;product_result4;term4;
         product_result3;term3;product_result2;term2;product_result1;
         term1;product_result0;term0] stack)
Proof
  strip_tac
  >> sg `registered_case10173_source_prefix_template
           center0 center1 center2 center3 center4 center5 =
         registered_case10173_cv_of_list
           (registered_case10173_ordinary_source_prefix_center
             center0 center1 center2 center3 center4 center5)`
  >- irule registered_case10173_source_prefix_as_ordinary_center
  >> sg `registered_case10173_source_prefix_template
           box0 box1 box2 box3 box4 box5 =
         registered_case10173_cv_of_list
           (registered_case10173_ordinary_source_prefix_box
             box0 box1 box2 box3 box4 box5)`
  >- irule registered_case10173_source_prefix_as_ordinary_box
  >> asm_rewrite_tac []
  >> simp
       [registered_case10173_ordinary_source_prefix_center_def,
        registered_case10173_ordinary_source_prefix_box_def,
        compute_registeredCase10173OrdinaryAddChainTraceEvalTheory.registered_case10173_ordinary_result_stack_def,
        compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_group_result_stack_def]
  >> irule
       (SIMP_RULE (srw_ss())
         [LET_THM,
          compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_group_result_stack_def]
         compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_six_group_prefix_trace)
  >> metis_tac []
QED

val _ = export_theory ();
