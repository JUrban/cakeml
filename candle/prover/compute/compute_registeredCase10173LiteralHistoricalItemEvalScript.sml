(*****************************************************************************
 * Exact typed identity for the authenticated historical source item.
 *
 * The packet-parametric evaluator theorem deliberately hid its result behind
 * an existential cv object.  The literal source checker must instead retain
 * the typed Taylor state so the following multiplication and additions can
 * be related to the same state.  This strengthening reuses the same
 * authenticated first/second-order refinements and exposes the canonical
 * row-expanded object for that typed result.
 *****************************************************************************)
Theory compute_registeredCase10173LiteralHistoricalItemEval
Ancestors
  compute_registeredCase10173HistoricalItemGeneralEval
  compute_registeredCase10173LiteralAddChainEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_taylor_object_complete_exact:
  bounded_taylor64_complete_decimal radii result_domain center_value
      center_gradient hessian = SOME result /\
  bounded_hessian64_rows hessian = SOME hessian_rows ==>
  registered_case10173_taylor_object result =
    bounded_taylor64_rows_object_cv result hessian_rows
Proof
  Cases_on `result`
  >> strip_tac
  >> imp_res_tac
       compute_registeredCase10173ResultSqrtContractTheory.registered_case10173_taylor_complete_decimal_hessian
  >> gvs
       [compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_object_def,
        compute_registeredCase10173LiteralAddChainEvalTheory.registered_case10173_taylor_rows_def]
QED

Theorem registered_case10173_literal_historical_item_packet_eval:
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
      compute_eval clock registered_case10173_historical_chunk16_ceqs
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
  rpt strip_tac
  >> fs
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def]
  >> every_case_tac
  >> gvs []
  >> fs []
  >> drule
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> strip_tac
  >> drule
       compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac
       compute_boundedObjectTaylorUnaryDecimalTheory.bounded_taylor64_complete_decimal_hessian_rows
  >> imp_res_tac
       compute_boundedObjectTaylorCompleteDecimalTheory.bounded_object_fs_taylor_complete_exact
  >> `bounded_case10173_literal_historical_item_decimal radii
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
      SOME historical_item` by
       (simp
          [compute_boundedCase10173LiteralSourceDecimalTheory.bounded_case10173_literal_historical_item_decimal_def]
        >> asm_rewrite_tac [])
  >> `registered_case10173_taylor_domain historical_item` by
       (Cases_on `historical_item`
        >> simp
             [compute_registeredCase10173ActualGroupProductEvalTheory.registered_case10173_taylor_domain_def]
        >> imp_res_tac
             compute_registeredCase10173ActualGroupProductEvalTheory.bounded_taylor64_complete_decimal_true_domain)
  >> `bounded_taylor64_well_formed historical_item` by
       metis_tac
         [compute_boundedTaylorCompleteDecimalTheory.bounded_taylor64_complete_decimal_some]
  >> `registered_case10173_taylor_object historical_item =
        bounded_taylor64_rows_object_cv historical_item hessian_rows` by
       metis_tac [registered_case10173_taylor_object_complete_exact]
  >> qexists_tac `historical_item`
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> conj_tac >- asm_rewrite_tac []
  >> rpt gen_tac
  >> strip_tac
  >> asm_rewrite_tac []
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> PURE_REWRITE_TAC [compute_execTheory.from_cv_def]
  >> irule
       (let
          val th0 =
            Q.INST
              [`center_boxes:cv` |-> `center_boxes`,
               `boxes:cv` |-> `boxes`,
               `encoded_radii` |->
                 `MAP
                    (\value.
                      (bounded_word64_object_cv value,Num 999999999999))
                    radii`,
               `root0:cv` |->
                 `bounded_interval64_object_cv center_root_delta`,
               `root1:cv` |->
                 `bounded_interval64_object_cv center_root_four_x0`,
               `root2:cv` |->
                 `bounded_interval64_object_cv box_root_delta`,
               `root3:cv` |->
                 `bounded_interval64_object_cv box_root_four_x0`,
               `roots_tail:cv` |-> `Num 0`,
               `result:cv` |->
                 `bounded_taylor64_rows_object_cv
                    historical_item hessian_rows`,
               `clock:num` |-> `clock`,
               `refs:hol_refs` |-> `refs`]
              compute_registeredCase10173HistItemCompleteObjectEvalTheory.registered_case10173_hist_item_complete_object_eval
          val th1 =
            SIMP_RULE std_ss [compute_execTheory.from_cv_def] th0
        in
          SIMP_RULE std_ss
            [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_as_signed64]
            th1
        end)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> conj_tac
  >- (imp_res_tac
        compute_registeredCase10173HistoricalItemGeneralEvalTheory.bounded_case10173_geometry_ok_lengths
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- ACCEPT_TAC
       (SIMP_RULE std_ss
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_as_signed64]
         compute_registeredCase10173HistoricalItemGeneralEvalTheory.registered_case10173_q_numerator_packet_radii)
  >> qexists_tac `[y0;y1;y2;y3;y4;y5]`
  >> qexists_tac `box_gradient`
  >> qexists_tac `box_value`
  >> qexists_tac `[x0;x1;x2;x3;x4;x5]`
  >> qexists_tac `center_gradient'`
  >> qexists_tac `center_value'`
  >> qexists_tac `hessian'`
  >> qexists_tac `hessian_rows`
  >> conj_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> conj_tac
  >- asm_rewrite_tac []
  >> conj_tac
  >- (simp [] >> intLib.ARITH_TAC)
  >> conj_tac
  >- asm_rewrite_tac []
  >> conj_tac
  >- (imp_res_tac
        compute_registeredCase10173HistoricalItemGeneralEvalTheory.bounded_case10173_geometry_ok_lengths
      >> imp_res_tac
           compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
      >> imp_res_tac
           compute_boundedObjectHistoricalFirstDecimalTheory.bounded_historical_dihedral_first64_decimal_source_trace
      >> imp_res_tac
           compute_boundedHistoricalDihedralSecondTheory.bounded_historical_replace_three_length
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- asm_rewrite_tac []
  >> conj_tac
  >- asm_rewrite_tac []
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173HistoricalFirstOrderGeneralEvalTheory.registered_case10173_historical_first_order_general_eval)
      >> conj_tac
      >- intLib.ARITH_TAC
      >> metis_tac [])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderGeneralEvalTheory.registered_case10173_historical_second_order_general_eval)
  >> conj_tac
  >- intLib.ARITH_TAC
  >> metis_tac []
QED

val _ = export_theory ();
