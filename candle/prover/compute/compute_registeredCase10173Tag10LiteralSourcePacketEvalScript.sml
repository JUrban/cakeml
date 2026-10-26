Theory compute_registeredCase10173Tag10LiteralSourcePacketEval
Ancestors
  compute_registeredCase10173Tag10LiteralSourceTraceEval
  compute_registeredCase10173LiteralInputAboveEval
Libs
  bossLib preamble

Theorem registered_case10173_tag10_literal_source_packet_eval:
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
  compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
    (App «candle_cv_case10173_hist_program_run»
      [from_cv center_boxes;from_cv boxes;
       from_cv
         (registered_case10173_q_cv_list
           (MAP
             (\value.
               (bounded_word64_object_cv value,Num 999999999999))
             radii));
       from_cv
         (bounded_interval64_object_cv_list
           [center_root_delta;center_root_four_x0;
            box_root_delta;box_root_four_x0]);
       from_cv
         (registered_case10173_cv_append
           (registered_case10173_source_prefix_template
             center0 center1 center2 center3 center4 center5)
           (Pair (Num 10) registered_case10173_source_suffix_template));
       from_cv
         (registered_case10173_cv_append
           (registered_case10173_source_prefix_template
             box0 box1 box2 box3 box4 box5)
           (Pair (Num 10) registered_case10173_source_suffix_template));
       from_cv (Num 0)]) (refs:hol_refs) =
    (M_success
      (from_cv
        (registered_case10173_ordinary_result_push
          (registered_case10173_taylor_object final_result) (Num 0))),refs)
Proof
  strip_tac
  >> `registered_case10173_eval_above 8208
        (App «candle_cv_fs_interval_list_of_q» [from_cv center_boxes])
        (bounded_interval64_object_cv_list [x0;x1;x2;x3;x4;x5])` by
       (irule registered_case10173_fs_interval_list_of_q_object_eval_above
        >> simp [])
  >> `registered_case10173_eval_above 8208
        (App «candle_cv_fs_list_of_q»
          [from_cv
            (registered_case10173_q_cv_list
              (MAP
                (\value.
                  (bounded_word64_object_cv value,Num 999999999999))
                radii))])
        (registered_case10173_word64_object_cv_list radii)` by
       (irule registered_case10173_decimal_radii_eval_above
        >> simp [])
  >> irule
       compute_registeredCase10173Tag10LiteralSourceTraceEvalTheory.registered_case10173_tag10_literal_source_program_eval
  >> conj_tac >- asm_rewrite_tac []
  >> qexists_tac `box_b_reciprocal`
  >> qexists_tac `box_diagonal_reciprocal`
  >> qexists_tac `box_root_derivative`
  >> qexists_tac `box_root_four_reciprocal`
  >> qexists_tac `box_root_logarithmic`
  >> qexists_tac `box_special_root_reciprocal`
  >> qexists_tac `box_u126_reciprocal`
  >> qexists_tac `box_u135_reciprocal`
  >> qexists_tac `box_u_reciprocal`
  >> qexists_tac `center_b_reciprocal`
  >> qexists_tac `center_root_derivative`
  >> qexists_tac `center_root_four_reciprocal`
  >> qexists_tac `center_special_root_reciprocal`
  >> qexists_tac `center_u_reciprocal`
  >> qexists_tac `certificate0`
  >> qexists_tac `certificate1`
  >> qexists_tac `certificate2`
  >> qexists_tac `certificate3`
  >> qexists_tac `certificate4`
  >> qexists_tac `certificate5`
  >> qexists_tac `radii`
  >> qexists_tac `x0`
  >> qexists_tac `x1`
  >> qexists_tac `x2`
  >> qexists_tac `x3`
  >> qexists_tac `x4`
  >> qexists_tac `x5`
  >> qexists_tac `y0`
  >> qexists_tac `y1`
  >> qexists_tac `y2`
  >> qexists_tac `y3`
  >> qexists_tac `y4`
  >> qexists_tac `y5`
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
