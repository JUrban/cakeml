(*****************************************************************************
 * Transfer the packet-parametric historical item theorem to the exact
 * corrected tag-10 equation environment.  The item call graph is unchanged;
 * only the surrounding private program opcode moved from 9 to 10.
 *****************************************************************************)
Theory compute_registeredCase10173Tag10LiteralHistoricalItemEval
Ancestors
  compute_registeredCase10173LiteralHistoricalItemEval
  compute_registeredCase10173Tag10HistItemCongruence
  compute_registeredCase10173HistoricalChunk16Tag10Data
Libs
  bossLib preamble

Theorem registered_case10173_tag10_literal_historical_item_packet_eval:
  bounded_packed_chars_case10173_decimal_packet_ok
      (BoundedCase10173Packet radii
        [x0;x1;x2;x3;x4;x5] [y0;y1;y2;y3;y4;y5]
        coordinate_sqrt_certificates
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
      SOME [y0;y1;y2;y3;y4;y5] ==>
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
    registered_case10173_taylor_domain historical_item /\
    bounded_taylor64_well_formed historical_item /\
    !clock refs.
      30000 < clock ==>
      compute_eval clock registered_case10173_historical_chunk16_tag10_ceqs
        (App «candle_cv_case10173_hist_item»
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
                box_root_delta;box_root_four_x0])])
        (refs:hol_refs) =
      (M_success
        (from_cv
          (Pair (Num 1)
            (registered_case10173_taylor_object historical_item))),refs)
Proof
  strip_tac
  >> drule_all_then strip_assume_tac
       compute_registeredCase10173LiteralHistoricalItemEvalTheory.registered_case10173_literal_historical_item_packet_eval
  >> qexists_tac `historical_item`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> rpt gen_tac
  >> strip_tac
  >> once_rewrite_tac
       [GSYM
          compute_registeredCase10173Tag10HistItemCongruenceTheory.registered_case10173_hist_item_old_tag10_eval_cong]
  >> qpat_x_assum `!clock refs. _` match_mp_tac
  >> asm_rewrite_tac []
QED

val _ = export_theory ();
