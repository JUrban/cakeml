(*****************************************************************************
 * Packet-parametric source-program preparation for the historical checker.
 *
 * An authenticated object job carries seven source square-root intervals for
 * each of the center and box programs.  The literal case-10173 source program
 * consumes exactly seven such entries.  This theory proves the exact-data
 * check and patch evaluation without replaying any numerical cell.
 *****************************************************************************)
Theory compute_registeredCase10173ProgramPreparationPacketEval
Ancestors
  compute_registeredCase10173ProductionGuardPacketEval
  compute_registeredCase10173AnalyticProgramSqrtEval
  compute_registeredCase10173GenuineProgramData
Libs
  bossLib preamble intLib

Theorem registered_case10173_positive_q_interval_list_length:
  !encoded intervals.
    bounded_object_positive_q_interval64_decimal_list encoded =
      SOME intervals ==>
    registered_case10173_cv_list_length encoded = LENGTH intervals
Proof
  ho_match_mp_tac
    compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_ind
  >> rw
       [compute_boundedObjectDecimalQTheory.bounded_object_positive_q_interval64_decimal_list_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_source_program_size_bound:
  2 * cv_size registered_case10173_genuine_source_program + 5 < 19000000
Proof
  simp
    [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_source_program_def,
     compute_registeredCase10173HistoricalChunk16DataTheory.registered_case10173_historical_chunk16_cexp_def,
     compute_pureFastTheory.compute_exp_to_cv_def,
     cvTheory.cv_size_def]
QED

Theorem registered_case10173_analytic_program_sqrt_data_exact_result_eval:
  registered_case10173_analytic_program_sqrt_data_exact_cv intervals program =
      Num 1 /\
  cv_size program + 2 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_analytic_program_sqrt_data_exact»
      [from_cv intervals;from_cv program]) (refs:hol_refs) =
    (M_success (Num 1),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `(M_success
          (from_cv
            (registered_case10173_analytic_program_sqrt_data_exact_cv
              intervals program)),refs)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_sqrt_data_exact_eval
      >> simp [])
  >> simp [compute_execTheory.from_cv_def]
QED

Theorem registered_case10173_analytic_program_patch_sqrt_result_eval:
  registered_case10173_analytic_program_patch_sqrt_cv intervals program =
      Pair remainder patched_program /\
  2 * cv_size program + 5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
    (App «candle_cv_analytic_program_patch_sqrt»
      [from_cv intervals;from_cv program]) (refs:hol_refs) =
    (M_success
      (Pair (from_cv remainder) (from_cv patched_program)),refs)
Proof
  strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `(M_success
          (from_cv
            (registered_case10173_analytic_program_patch_sqrt_cv
              intervals program)),refs)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_eval
      >> simp [])
  >> simp [compute_execTheory.from_cv_def]
QED

Definition registered_case10173_analytic_program_sqrt_count_def:
  registered_case10173_analytic_program_sqrt_count
      (Pair instruction program : cv) =
    (if registered_case10173_analytic_instruction_is_sqrt_cv instruction =
          Num 1
     then SUC (registered_case10173_analytic_program_sqrt_count program)
     else registered_case10173_analytic_program_sqrt_count program) /\
  registered_case10173_analytic_program_sqrt_count (Num n) = 0
End

Theorem registered_case10173_analytic_program_sqrt_data_exact_from_count:
  !program sqrt_data.
    registered_case10173_cv_list_length sqrt_data =
      registered_case10173_analytic_program_sqrt_count program ==>
    registered_case10173_analytic_program_sqrt_data_exact_cv sqrt_data
      program = Num 1
Proof
  Induct_on `program`
  >- (gen_tac
      >> Cases_on `sqrt_data`
      >> simp
           [registered_case10173_analytic_program_sqrt_count_def,
            compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
            registered_case10173_analytic_program_sqrt_data_exact_cv_def])
  >> gen_tac
  >> Cases_on `sqrt_data`
  >> simp
       [registered_case10173_analytic_program_sqrt_count_def,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def,
        registered_case10173_analytic_program_sqrt_data_exact_cv_def]
  >> Cases_on
       `registered_case10173_analytic_instruction_is_sqrt_cv program = Num 1`
  >> fs []
  >> strip_tac
  >> qpat_x_assum
       `!sqrt_data.
          registered_case10173_cv_list_length sqrt_data =
            registered_case10173_analytic_program_sqrt_count program' ==>
          _`
       (qspec_then `Num n` mp_tac)
  >> simp
       [compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_cv_list_length_def]
QED

Theorem registered_case10173_source_program_sqrt_count:
  registered_case10173_analytic_program_sqrt_count
    registered_case10173_genuine_source_program = 7
Proof
  EVAL_TAC
QED

Theorem registered_case10173_source_program_seven_sqrt_data_exact:
  registered_case10173_cv_list_length sqrt_data = 7 ==>
  registered_case10173_analytic_program_sqrt_data_exact_cv sqrt_data
      registered_case10173_genuine_source_program = Num 1
Proof
  strip_tac
  >> irule registered_case10173_analytic_program_sqrt_data_exact_from_count
  >> simp [registered_case10173_source_program_sqrt_count]
QED

Theorem registered_case10173_add_coordinate_sqrts_decimal_lengths:
  !certificates coefficients radii center_environment box_environment
   index accumulator result.
    bounded_case10173_add_coordinate_sqrts_decimal radii
      center_environment box_environment certificates coefficients
      index accumulator = SOME result ==>
    LENGTH certificates = LENGTH coefficients /\
    LENGTH certificates + index = 6
Proof
  Induct_on `certificates`
  >- (rpt gen_tac
      >> Cases_on `coefficients`
      >> rw
           [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_add_coordinate_sqrts_decimal_def]
      >> gvs [])
  >> rpt gen_tac
  >> Cases_on `h`
  >> Cases_on `coefficients`
  >> rw
       [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_add_coordinate_sqrts_decimal_def]
  >> every_case_tac
  >> gvs []
  >> first_x_assum drule
  >> strip_tac
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_sqrt64_center_intervals_length:
  !certificates.
    LENGTH (bounded_case10173_sqrt64_center_intervals certificates) =
      LENGTH certificates
Proof
  Induct
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_center_intervals_def]
  >> Cases_on `h`
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_center_intervals_def]
QED

Theorem registered_case10173_sqrt64_box_intervals_length:
  !certificates.
    LENGTH (bounded_case10173_sqrt64_box_intervals certificates) =
      LENGTH certificates
Proof
  Induct
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_box_intervals_def]
  >> Cases_on `h`
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_sqrt64_box_intervals_def]
QED

Theorem registered_case10173_object_checked_cell_sqrt_certificate_length:
  bounded_object_case10173_checked_cell64_decimal radii
    center_environment box_environment coordinate_sqrt_certificates
    center_root_delta center_root_four_x0 center_reciprocals
    box_root_delta box_root_four_x0 box_reciprocals = SOME result ==>
  LENGTH coordinate_sqrt_certificates = 6
Proof
  strip_tac
  >> subgoal
       `?initial roots_and_constant.
          bounded_case10173_add_coordinate_sqrts_decimal radii
            center_environment box_environment coordinate_sqrt_certificates
            bounded_case10173_root_coefficients_decimal 0 initial =
          SOME roots_and_constant`
  >- (qpat_x_assum
        `bounded_object_case10173_checked_cell64_decimal _ _ _ _ _ _ _ _ _ _ =
           SOME _`
        mp_tac
      >> simp
           [compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_object_case10173_checked_cell64_decimal_def]
      >> rpt (TOP_CASE_TAC >> gvs [])
      >> metis_tac [])
  >> imp_res_tac registered_case10173_add_coordinate_sqrts_decimal_lengths
  >> fs
       [compute_boundedCase10173HistoricalCellDecimalTheory.bounded_case10173_root_coefficients_decimal_def]
QED

Theorem registered_case10173_packet_sqrt_root_lengths:
  bounded_packed_chars_case10173_decimal_packet_ok packet ==>
  LENGTH (FST (bounded_case10173_decimal_packet_sqrt_roots packet)) = 6 /\
  LENGTH (SND (bounded_case10173_decimal_packet_sqrt_roots packet)) = 6
Proof
  strip_tac
  >> drule
       compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_ok_object_sound
  >> Cases_on `packet`
  >> simp
       [compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packet_object_ok_def]
  >> strip_tac
  >> imp_res_tac
       registered_case10173_object_checked_cell_sqrt_certificate_length
  >> simp
       [compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_def,
        registered_case10173_sqrt64_center_intervals_length,
        registered_case10173_sqrt64_box_intervals_length]
QED

Theorem registered_case10173_authenticated_source_program_preparation:
  bounded_packed_chars_case10173_decimal_packet_ok packet /\
  bounded_case10173_decimal_packet_root_inputs_exact
    packet object_job root_record ==>
  ?box_sqrt_data center_sqrt_data boxes
   box_remainder box_program center_remainder center_program.
    object_job = Pair box_sqrt_data (Pair center_sqrt_data boxes) /\
    registered_case10173_analytic_program_patch_sqrt_cv box_sqrt_data
      registered_case10173_genuine_source_program =
        Pair box_remainder box_program /\
    registered_case10173_analytic_program_patch_sqrt_cv center_sqrt_data
      registered_case10173_genuine_source_program =
        Pair center_remainder center_program /\
    !clock refs.
      20000000 <= clock ==>
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv box_sqrt_data;
           from_cv registered_case10173_genuine_source_program])
        (refs:hol_refs) = (M_success (Num 1),refs) /\
      compute_eval clock registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [from_cv box_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) refs =
        (M_success
          (from_cv (Pair box_remainder box_program)),refs) /\
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_sqrt_data_exact»
          [from_cv center_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) refs =
        (M_success (Num 1),refs) /\
      compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (App «candle_cv_analytic_program_patch_sqrt»
          [from_cv center_sqrt_data;
           from_cv registered_case10173_genuine_source_program]) refs =
        (M_success
          (from_cv (Pair center_remainder center_program)),refs)
Proof
  strip_tac
  >> fs
       [compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_decimal_packet_root_inputs_exact_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_input_binding_def,
        compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_exact_auxiliary_binding_def]
  >> imp_res_tac
       compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet_sqrt_roots_binding_components
  >> imp_res_tac registered_case10173_packet_sqrt_root_lengths
  >> imp_res_tac registered_case10173_positive_q_interval_list_length
  >> subgoal `registered_case10173_cv_list_length box_sqrt_data = 7`
  >- gvs []
  >> subgoal `registered_case10173_cv_list_length center_sqrt_data = 7`
  >- gvs []
  >> qspecl_then
       [`registered_case10173_genuine_source_program`,`box_sqrt_data`]
       strip_assume_tac
       compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_pair
  >> qspecl_then
       [`registered_case10173_genuine_source_program`,`center_sqrt_data`]
       strip_assume_tac
       compute_registeredCase10173AnalyticProgramSqrtEvalTheory.registered_case10173_analytic_program_patch_sqrt_cv_pair
  >> qexists_tac `box_sqrt_data`
  >> qexists_tac `center_sqrt_data`
  >> qexists_tac `source_boxes`
  >> qexists_tac `remaining`
  >> qexists_tac `patched_program`
  >> qexists_tac `remaining'`
  >> qexists_tac `patched_program'`
  >> simp []
  >> rpt gen_tac
  >> strip_tac
  >> imp_res_tac registered_case10173_source_program_seven_sqrt_data_exact
  >> rpt conj_tac
  >- (irule
        registered_case10173_analytic_program_sqrt_data_exact_result_eval
      >> simp []
      >> mp_tac registered_case10173_source_program_size_bound
      >> intLib.ARITH_TAC)
  >- (irule registered_case10173_analytic_program_patch_sqrt_result_eval
      >> simp []
      >> mp_tac registered_case10173_source_program_size_bound
      >> intLib.ARITH_TAC)
  >- (irule
        registered_case10173_analytic_program_sqrt_data_exact_result_eval
      >> simp []
      >> mp_tac registered_case10173_source_program_size_bound
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_analytic_program_patch_sqrt_result_eval
  >> simp []
  >> mp_tac registered_case10173_source_program_size_bound
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
