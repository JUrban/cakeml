(*****************************************************************************
 * Complete typed trace for one successful literal case-10173 source packet.
 *
 * This is the composition boundary promised by the fast-theorem plan: the
 * exact 31-instruction source prefix, the authenticated historical opcode-9
 * item, and the exact 15-instruction literal suffix all refer to the same
 * typed Taylor states produced by the bounded checker.  No numerical result
 * is introduced as an unrelated existential cv value.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralSourceTraceEval
Ancestors
  compute_registeredCase10173LiteralSourceComponentsEval
  compute_registeredCase10173CompleteSourceTraceEval
Libs
  bossLib preamble

Theorem registered_case10173_literal_source_program_trace:
  LENGTH radii = 6 /\
  bounded_packed_chars_case10173_decimal_packet_ok
    (BoundedCase10173Packet radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME [x0;x1;x2;x3;x4;x5] /\
  bounded_object_positive_q_interval64_decimal_list boxes =
    SOME [y0;y1;y2;y3;y4;y5] /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
    (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5]) /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  source_radii =
    registered_case10173_q_cv_list
      (MAP
        (\value.
          (bounded_word64_object_cv value,Num 999999999999))
        radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    [x0;x1;x2;x3;x4;x5]
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
  bounded_case10173_literal_source_decimal
    (BoundedCase10173Packet radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) =
    SOME final_result ==>
  ?historical_item.
    bounded_case10173_literal_historical_item_decimal radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal] =
      SOME historical_item /\
    registered_case10173_source_program_trace 8215 30000
      center_boxes boxes source_radii
      (bounded_interval64_object_cv_list
        [center_root_delta;center_root_four_x0;
         box_root_delta;box_root_four_x0])
      (Pair (Num 1) (registered_case10173_taylor_object historical_item))
      (registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          center0 center1 center2 center3 center4 center5)
        (Pair (Num 9) registered_case10173_source_suffix_template))
      (registered_case10173_cv_append
        (registered_case10173_source_prefix_template
          box0 box1 box2 box3 box4 box5)
        (Pair (Num 9) registered_case10173_source_suffix_template))
      (Num 0)
      (registered_case10173_ordinary_result_push
        (registered_case10173_taylor_object final_result) (Num 0))
Proof
  strip_tac
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173LiteralSourceComponentsEvalTheory.registered_case10173_literal_source_components_exact
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173LiteralHistoricalItemEvalTheory.registered_case10173_literal_historical_item_packet_eval
  >> qexists_tac `historical_item`
  >> conj_tac
  >- (asm_rewrite_tac [] >> metis_tac [])
  >> `historical_item' = historical_item` by
       (qpat_x_assum `_ = SOME historical_item'` mp_tac
        >> qpat_x_assum `_ = SOME historical_item` mp_tac
        >> simp [])
  >> qpat_x_assum `historical_item' = historical_item` SUBST_ALL_TAC
  >> mp_tac
       (Q.INST
         [`dimensions` |-> `[x0;x1;x2;x3;x4;x5]`,
          `radii` |-> `radii`,
          `summands` |->
            `[registered_case10173_constant_taylor
                registered_case10173_ordinary_term56_value;
              product5;
              registered_case10173_constant_taylor
                registered_case10173_ordinary_term56_value;
              product4;
              registered_case10173_constant_taylor
                registered_case10173_ordinary_term4_value;
              product3;
              registered_case10173_constant_taylor
                registered_case10173_ordinary_term23_value;
              product2;
              registered_case10173_constant_taylor
                registered_case10173_ordinary_term23_value;
              product1;
              registered_case10173_constant_taylor
                registered_case10173_ordinary_term1_value;
              product0;
              registered_case10173_constant_taylor
                registered_case10173_ordinary_term0_value]`,
          `historical_item` |-> `historical_item`,
          `scaled_historical` |-> `scaled_historical`,
          `final_result` |-> `final_result`,
          `center_boxes:cv` |-> `center_boxes`,
          `boxes:cv` |-> `boxes`,
          `source_radii:cv` |-> `source_radii`]
         (INST_TYPE [alpha |-> ``:cv``]
           compute_registeredCase10173LiteralSuffixContractEvalTheory.registered_case10173_literal_suffix_numeric_contract))
  >> impl_tac
  >- (asm_rewrite_tac [] >> simp [])
  >> strip_tac
  >> mp_tac
       (Q.INST
         [`dimensions` |-> `[x0;x1;x2;x3;x4;x5]`,
          `radii` |-> `radii`,
          `center_environment` |-> `[x0;x1;x2;x3;x4;x5]`,
          `center_boxes:cv` |-> `center_boxes`,
          `boxes:cv` |-> `boxes`,
          `source_radii:cv` |-> `source_radii`,
          `certificate0` |-> `certificate0`,
          `certificate1` |-> `certificate1`,
          `certificate2` |-> `certificate2`,
          `certificate3` |-> `certificate3`,
          `certificate4` |-> `certificate4`,
          `certificate5` |-> `certificate5`,
          `product0` |-> `product0`,
          `product1` |-> `product1`,
          `product2` |-> `product2`,
          `product3` |-> `product3`,
          `product4` |-> `product4`,
          `product5` |-> `product5`,
          `center0:cv` |-> `center0`,
          `center1:cv` |-> `center1`,
          `center2:cv` |-> `center2`,
          `center3:cv` |-> `center3`,
          `center4:cv` |-> `center4`,
          `center5:cv` |-> `center5`,
          `box0:cv` |-> `box0`,
          `box1:cv` |-> `box1`,
          `box2:cv` |-> `box2`,
          `box3:cv` |-> `box3`,
          `box4:cv` |-> `box4`,
          `box5:cv` |-> `box5`,
          `stack:cv` |-> `Num 0`]
         compute_registeredCase10173LiteralPrefixStackEvalTheory.registered_case10173_literal_products_source_prefix_taylor_stack_trace)
  >> impl_tac
  >- (asm_rewrite_tac [] >> simp [])
  >> strip_tac
  >> `registered_case10173_source_suffix_template =
        registered_case10173_cv_of_list
          (registered_case10173_ordinary_suffix_instructions
            (MAP registered_case10173_taylor_object
              [registered_case10173_constant_taylor
                 registered_case10173_ordinary_term56_value;
               product5;
               registered_case10173_constant_taylor
                 registered_case10173_ordinary_term56_value;
               product4;
               registered_case10173_constant_taylor
                 registered_case10173_ordinary_term4_value;
               product3;
               registered_case10173_constant_taylor
                 registered_case10173_ordinary_term23_value;
               product2;
               registered_case10173_constant_taylor
                 registered_case10173_ordinary_term23_value;
               product1;
               registered_case10173_constant_taylor
                 registered_case10173_ordinary_term1_value;
               product0;
               registered_case10173_constant_taylor
                 registered_case10173_ordinary_term0_value]))` by
       (irule
          compute_registeredCase10173OrdinarySuffixTraceEvalTheory.registered_case10173_source_suffix_as_ordinary_suffix
        >> simp [])
  >> drule
       compute_registeredCase10173OrdinarySuffixTraceEvalTheory.registered_case10173_ordinary_suffix_trace
  >> disch_then (qspec_then `Num 0` assume_tac)
  >> irule
       compute_registeredCase10173CompleteSourceTraceEvalTheory.registered_case10173_prefix_item_suffix_source_trace
  >> conj_tac
  >- simp
       [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_source_prefix_template_length]
  >> conj_tac
  >- fs
       [compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_item_eval_above_def]
  >> qexists_tac
       `registered_case10173_ordinary_result_stack
          (MAP registered_case10173_taylor_object
            [registered_case10173_constant_taylor
               registered_case10173_ordinary_term56_value;
             product5;
             registered_case10173_constant_taylor
               registered_case10173_ordinary_term56_value;
             product4;
             registered_case10173_constant_taylor
               registered_case10173_ordinary_term4_value;
             product3;
             registered_case10173_constant_taylor
               registered_case10173_ordinary_term23_value;
             product2;
             registered_case10173_constant_taylor
               registered_case10173_ordinary_term23_value;
             product1;
             registered_case10173_constant_taylor
               registered_case10173_ordinary_term1_value;
             product0;
             registered_case10173_constant_taylor
               registered_case10173_ordinary_term0_value])
          (Num 0)`
  >> conj_tac >- asm_rewrite_tac []
  >> qpat_x_assum
       `registered_case10173_ordinary_program_trace (8210 + 5)
          center_boxes boxes source_radii _ _ _ _` mp_tac
  >> asm_rewrite_tac []
  >> simp
       [compute_registeredCase10173OrdinaryPrefixTraceEvalTheory.registered_case10173_ordinary_result_push_def]
QED

Theorem registered_case10173_literal_source_program_length:
  registered_case10173_cv_list_length
    (registered_case10173_cv_append
      (registered_case10173_source_prefix_template
        item0 item1 item2 item3 item4 item5)
      (Pair (Num 9) registered_case10173_source_suffix_template)) = 47
Proof
  EVAL_TAC
QED

(* Execute the exact source-shaped trace without replaying the generic
 * numerical evaluator.  The bound is structural: 8215 for any ordinary
 * instruction, 30000 for the one authenticated historical item, 47 source
 * instructions, and the four units required by the trace interpreter. *)
Theorem registered_case10173_literal_source_program_eval:
  LENGTH radii = 6 /\
  bounded_packed_chars_case10173_decimal_packet_ok
    (BoundedCase10173Packet radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
    SOME [x0;x1;x2;x3;x4;x5] /\
  bounded_object_positive_q_interval64_decimal_list boxes =
    SOME [y0;y1;y2;y3;y4;y5] /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
    (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5]) /\
  registered_case10173_eval_above 8208
    (App «candle_cv_fs_list_of_q» [from_cv source_radii])
    (registered_case10173_word64_object_cv_list radii) /\
  source_radii =
    registered_case10173_q_cv_list
      (MAP
        (\value.
          (bounded_word64_object_cv value,Num 999999999999))
        radii) /\
  bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
    [x0;x1;x2;x3;x4;x5]
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
  bounded_case10173_literal_source_decimal
    (BoundedCase10173Packet radii
      [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
      center_root_delta center_root_four_x0
      [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal]
      box_root_delta box_root_four_x0
      [box_root_derivative;box_root_logarithmic;
       box_root_four_reciprocal;box_diagonal_reciprocal;
       box_u_reciprocal;box_special_root_reciprocal;
       box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal]) =
    SOME final_result /\
  38266 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_case10173_hist_program_run»
      [from_cv center_boxes;from_cv boxes;from_cv source_radii;
       from_cv
         (bounded_interval64_object_cv_list
           [center_root_delta;center_root_four_x0;
            box_root_delta;box_root_four_x0]);
       from_cv
         (registered_case10173_cv_append
           (registered_case10173_source_prefix_template
             center0 center1 center2 center3 center4 center5)
           (Pair (Num 9) registered_case10173_source_suffix_template));
       from_cv
         (registered_case10173_cv_append
           (registered_case10173_source_prefix_template
             box0 box1 box2 box3 box4 box5)
           (Pair (Num 9) registered_case10173_source_suffix_template));
       from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_ordinary_result_push
          (registered_case10173_taylor_object final_result) (Num 0))),refs)
Proof
  strip_tac
  >> drule_all_then strip_assume_tac
       registered_case10173_literal_source_program_trace
  >> irule
       compute_registeredCase10173CompleteSourceTraceEvalTheory.registered_case10173_source_program_trace_sound
  >> qexists_tac
       `Pair (Num 1) (registered_case10173_taylor_object historical_item)`
  >> qexists_tac `30000`
  >> qexists_tac `8215`
  >> conj_tac
  >- simp [registered_case10173_literal_source_program_length]
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
