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

val _ = export_theory ();
