(*****************************************************************************
 * Packet-parametric refinement for one authenticated historical item.
 *
 * A successful strengthened decimal packet now includes the standalone
 * Taylor completion used by the registered historical evaluator.  This
 * theorem composes that certificate with the packet-independent first- and
 * second-order evaluator refinements.  No closed cell or per-cell evaluator
 * replay occurs here.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalItemGeneralEval
Ancestors
  compute_registeredCase10173HistoricalFirstOrderGeneralEval
  compute_registeredCase10173HistoricalSecondOrderGeneralEval
  compute_registeredCase10173HistItemCompleteObjectEval
  compute_registeredCase10173RadiusBinding
  compute_boundedCase10173PackedDecimalBatch
Libs
  bossLib preamble intLib

Theorem registered_case10173_q_numerator_packet_radii:
  registered_case10173_q_numerator_cv_list
      (MAP
        (\value.
          (bounded_word64_object_cv value,Num 999999999999))
        radii) =
    registered_case10173_word64_object_cv_list radii
Proof
  Induct_on `radii`
  >- (PURE_REWRITE_TAC
        [listTheory.MAP,
         compute_registeredCase10173RadiiEvalTheory.registered_case10173_q_numerator_cv_list_def,
         compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_word64_object_cv_list_def]
      >> REFL_TAC)
  >> strip_tac
  >> PURE_REWRITE_TAC
       [listTheory.MAP,
        compute_registeredCase10173TaylorDotEvalTheory.registered_case10173_word64_object_cv_list_def]
  >> BETA_TAC
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173RadiiEvalTheory.registered_case10173_q_numerator_cv_list_def]
  >> asm_rewrite_tac []
QED

Theorem bounded_case10173_geometry_ok_lengths:
  !boxes centers radii count.
    bounded_case10173_geometry_ok boxes centers radii count ==>
    LENGTH boxes = LENGTH centers /\
    LENGTH centers = LENGTH radii /\
    LENGTH boxes + count = 6
Proof
  Induct
  >> Cases_on `centers`
  >> Cases_on `radii`
  >> simp
       [compute_boundedCase10173HistoricalCellTheory.bounded_case10173_geometry_ok_def]
  >> rpt strip_tac
  >> first_x_assum drule
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_historical_item_packet_eval:
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
  ?result.
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
    (M_success (from_cv (Pair (Num 1) result)),refs)
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
  >> qexists_tac `bounded_taylor64_rows_object_cv historical_item hessian_rows`
  >> rpt gen_tac
  >> strip_tac
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
  >- (imp_res_tac bounded_case10173_geometry_ok_lengths
      >> simp []
      >> intLib.ARITH_TAC)
  >> conj_tac
  >- ACCEPT_TAC
       (SIMP_RULE std_ss
         [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_as_signed64]
         registered_case10173_q_numerator_packet_radii)
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
  >- (imp_res_tac bounded_case10173_geometry_ok_lengths
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

Theorem registered_case10173_historical_item_packet_accessor_eval:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_object_positive_q_interval64_decimal_list center_boxes =
      SOME (bounded_case10173_packet_center_environment packet) /\
  bounded_object_positive_q_interval64_decimal_list boxes =
      SOME (bounded_case10173_packet_box_environment packet) ==>
  ?result.
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
               (bounded_case10173_packet_radii packet)));
         from_cv
           (bounded_interval64_object_cv_list
             (bounded_case10173_packet_root_intervals packet))])
      (refs:hol_refs) =
    (M_success (from_cv (Pair (Num 1) result)),refs)
Proof
  Cases_on `packet`
  >> simp
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
        compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
        compute_registeredCase10173RadiusBindingTheory.bounded_case10173_packet_radii_def,
        compute_boundedCase10173RootBindingTheory.bounded_case10173_packet_root_intervals_def]
  >> rpt strip_tac
  >> fs
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def]
  >> every_case_tac
  >> gvs []
  >> drule
       compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell_accepts_decimal_contract
  >> strip_tac
  >> drule
       compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_case10173_checked_cell64_decimal_source_trace
  >> strip_tac
  >> imp_res_tac bounded_case10173_geometry_ok_lengths
  >> subgoal `LENGTH l0 = 6`
  >- intLib.ARITH_TAC
  >> subgoal `LENGTH l1 = 6`
  >- intLib.ARITH_TAC
  >> qpat_x_assum `LENGTH l0 = LENGTH l` kall_tac
  >> qpat_x_assum `LENGTH l1 = LENGTH l0` kall_tac
  >> qpat_x_assum `LENGTH l1 + 0 = 6` kall_tac
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> irule
       (SIMP_RULE std_ss
         [compute_execTheory.from_cv_def,
          compute_boundedObjectTaylorCompleteDecimalTheory.bounded_word64_object_cv_as_signed64]
         registered_case10173_historical_item_packet_eval)
  >> simp
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_def]
  >> metis_tac []
QED

val _ = export_theory ();
