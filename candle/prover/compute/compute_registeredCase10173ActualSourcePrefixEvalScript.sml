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

val _ = export_theory ();
