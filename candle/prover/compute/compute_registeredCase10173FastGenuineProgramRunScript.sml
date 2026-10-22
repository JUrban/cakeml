(*****************************************************************************
 * Execute the corrected fast source trace for the genuine first NL job.
 *****************************************************************************)
Theory compute_registeredCase10173FastGenuineProgramRun
Ancestors
  compute_registeredCase10173FastGenuineProgramIdentity
  compute_registeredCase10173LiteralSourcePacketEval
  compute_registeredCase10173FastLiteralResultData
  compute_registeredCase10173GenuineHistItemEval
  compute_registeredCase10173GenuineProgramMemoEval
Libs
  bossLib preamble

Theorem registered_case10173_actual_sqrt_prefix_six_ignores_tail:
  bounded_case10173_actual_sqrt_source_prefix_exact 6 index radii environment
      (registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5;center_tail])
      (registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5;box_tail])
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5] =
  bounded_case10173_actual_sqrt_source_prefix_exact 6 index radii environment
      (registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5])
      (registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5])
      [certificate0;certificate1;certificate2;
       certificate3;certificate4;certificate5]
Proof
  PURE_REWRITE_TAC
    [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def]
  >> Cases_on `certificate0`
  >> Cases_on `certificate1`
  >> Cases_on `certificate2`
  >> Cases_on `certificate3`
  >> Cases_on `certificate4`
  >> Cases_on `certificate5`
  >> PURE_REWRITE_TAC [DECIDE ``6 = SUC 5``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``5 = SUC 4``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``4 = SUC 3``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``3 = SUC 2``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``2 = SUC 1``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> PURE_REWRITE_TAC [DECIDE ``1 = SUC 0``]
  >> PURE_REWRITE_TAC
       [compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_actual_sqrt_source_prefix_exact_def]
  >> simp []
QED

Theorem registered_case10173_actual_sqrt_prefix_six_ignores_tail_length:
  LENGTH certificates = 6 ==>
  bounded_case10173_actual_sqrt_source_prefix_exact 6 index radii environment
      (registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5;center_tail])
      (registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5;box_tail])
      certificates =
  bounded_case10173_actual_sqrt_source_prefix_exact 6 index radii environment
      (registered_case10173_cv_of_list
        [center0;center1;center2;center3;center4;center5])
      (registered_case10173_cv_of_list
        [box0;box1;box2;box3;box4;box5])
      certificates
Proof
  strip_tac
  >> gvs
       [listTheory.LENGTH_EQ_NUM_compute,
        registered_case10173_actual_sqrt_prefix_six_ignores_tail]
QED

Theorem registered_case10173_first_job_object_components:
  registered_case10173_first_job_object_job =
      Pair box_sqrt_data (Pair center_sqrt_data source_boxes) ==>
  registered_case10173_first_job_box_sqrt_data = box_sqrt_data /\
  registered_case10173_first_job_center_sqrt_data = center_sqrt_data /\
  registered_case10173_first_job_boxes = source_boxes
Proof
  strip_tac
  >> PURE_REWRITE_TAC
    [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_first_job_box_sqrt_data_def,
     compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_first_job_center_sqrt_data_def,
     compute_registeredCase10173RootRecordValueTheory.registered_case10173_first_job_boxes_def]
  >> PURE_ONCE_REWRITE_TAC
       [compute_registeredCase10173FastGenuineContractDataTheory.registered_case10173_first_job_object_job_exact]
  >> asm_simp_tac std_ss []
  >> simp []
QED

Theorem registered_case10173_genuine_encoded_radii_source_exact:
  registered_case10173_genuine_encoded_radii =
  registered_case10173_q_cv_list
    (MAP (\value.
      (bounded_word64_object_cv value,Num 999999999999))
      registered_case10173_historical_radii_words)
Proof
  simp
    [compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_encoded_radii_def,
     compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_def]
QED

Theorem registered_case10173_historical_radii_length:
  LENGTH registered_case10173_historical_radii_words = 6
Proof
  simp
    [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
     compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
     compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
QED

Theorem registered_case10173_genuine_fast_literal_program_run_eval:
  38266 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_case10173_hist_program_run»
      [from_cv registered_case10173_genuine_center_boxes;
       from_cv registered_case10173_first_job_boxes;
       from_cv registered_case10173_genuine_encoded_radii;
       from_cv registered_case10173_first_job_roots;
       from_cv registered_case10173_genuine_spliced_center_program;
       from_cv registered_case10173_genuine_spliced_box_program;
       from_cv (Num 0)]) (refs:hol_refs) =
  (M_success
    (from_cv
      (registered_case10173_ordinary_result_push
        (registered_case10173_taylor_object
          registered_case10173_fast_literal_result)
        (Num 0))),refs)
Proof
  strip_tac
  >> mp_tac
       (MATCH_MP
         compute_boundedCase10173ActualSqrtOperandTheory.bounded_case10173_source_actual_sqrt_contract_components
         compute_registeredCase10173FastGenuineContractDataTheory.registered_case10173_first_job_source_actual_sqrt_contract)
  >> strip_tac
  >> mp_tac
       compute_registeredCase10173FastGenuineProgramIdentityTheory.registered_case10173_genuine_spliced_programs_exact
  >> strip_tac
  >> mp_tac
       compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_source_inputs_exact
  >> strip_tac
  >> imp_res_tac registered_case10173_first_job_object_components
  >> `bounded_case10173_packet_well_shaped
        (BoundedCase10173Packet radii center_environment box_environment
          coordinate_sqrt_certificates center_root_delta center_root_four_x0
          center_reciprocals box_root_delta box_root_four_x0
          box_reciprocals)` by
       metis_tac
         [compute_registeredCase10173FastGenuinePacketDataTheory.registered_case10173_source_aligned_decimal_packet_well_shaped]
  >> qpat_x_assum `bounded_case10173_packet_well_shaped _` mp_tac
  >> simp
       [compute_boundedCase10173PacketTheory.bounded_case10173_packet_well_shaped_def]
  >> strip_tac
  >> subgoal
       `bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
          center_environment
          (registered_case10173_cv_of_list
            [center0;center1;center2;center3;center4;center5])
          (registered_case10173_cv_of_list
            [box0;box1;box2;box3;box4;box5])
          coordinate_sqrt_certificates` >-
       (qpat_x_assum
          `bounded_case10173_actual_sqrt_source_prefix_exact 6 0 radii
             center_environment center_sqrt_data box_sqrt_data
             coordinate_sqrt_certificates`
          mp_tac
        >> qpat_x_assum
             `registered_case10173_first_job_box_sqrt_data = box_sqrt_data`
             (fn th => PURE_ONCE_REWRITE_TAC [GSYM th])
        >> qpat_x_assum
             `registered_case10173_first_job_center_sqrt_data =
                center_sqrt_data`
             (fn th => PURE_ONCE_REWRITE_TAC [GSYM th])
        >> qpat_x_assum
             `registered_case10173_first_job_box_sqrt_data =
                registered_case10173_cv_of_list
                  [box0;box1;box2;box3;box4;box5;box6]`
             (fn th => PURE_ONCE_REWRITE_TAC [th])
        >> qpat_x_assum
             `registered_case10173_first_job_center_sqrt_data =
                registered_case10173_cv_of_list
                  [center0;center1;center2;center3;center4;center5;center6]`
             (fn th => PURE_ONCE_REWRITE_TAC [th])
        >> simp
             [registered_case10173_actual_sqrt_prefix_six_ignores_tail_length])
  >> subgoal
       `center_boxes = registered_case10173_genuine_center_boxes` >-
       (mp_tac
          compute_registeredCase10173GenuineProgramMemoEvalTheory.registered_case10173_genuine_center_boxes_exact
        >> asm_rewrite_tac []
        >> simp [])
  >> subgoal
       `registered_case10173_historical_radii_words = radii` >-
       (PURE_REWRITE_TAC
          [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def]
        >> qpat_x_assum
             `bounded_case10173_decimal_packet0_source_aligned =
                BoundedCase10173Packet radii center_environment
                  box_environment coordinate_sqrt_certificates
                  center_root_delta center_root_four_x0 center_reciprocals
                  box_root_delta box_root_four_x0 box_reciprocals`
             (fn th => PURE_ONCE_REWRITE_TAC [th])
        >> simp [])
  >> gvs [listTheory.LENGTH_EQ_NUM_compute]
  >> PURE_ONCE_REWRITE_TAC
       [registered_case10173_genuine_encoded_radii_source_exact]
  >> qpat_x_assum
       `registered_case10173_cv_append
          (registered_case10173_source_prefix_template
            center0 center1 center2 center3 center4 center5) _ =
        registered_case10173_genuine_spliced_center_program`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th])
  >> qpat_x_assum
       `registered_case10173_cv_append
          (registered_case10173_source_prefix_template
            box0 box1 box2 box3 box4 box5) _ =
        registered_case10173_genuine_spliced_box_program`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th])
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173LiteralSourcePacketEvalTheory.registered_case10173_literal_source_packet_eval)
  >> assume_tac
       compute_registeredCase10173FastGenuinePacketDataTheory.registered_case10173_source_aligned_decimal_packet_ok
  >> assume_tac
       compute_registeredCase10173FastLiteralResultDataTheory.registered_case10173_fast_literal_result_exact
  >> qpat_x_assum
       `BoundedCase10173Packet _ _ _ _ _ _ _ _ _ _ =
          bounded_case10173_decimal_packet0_source_aligned`
       (fn th => fs
         [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
          compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_root_delta_def,
          compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_root_four_x0_def,
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_decimal_def,
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_root_delta_def,
          compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_root_four_x0_def,
          compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
          compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
          GSYM th])
  >> fs
       [compute_registeredCase10173ProgramTemplatePacketEvalTheory.registered_case10173_cv_of_list_def]
  >> simp [registered_case10173_historical_radii_length]
  >> metis_tac []
QED

val _ = export_theory ();
