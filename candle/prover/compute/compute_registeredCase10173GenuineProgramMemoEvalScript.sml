(*****************************************************************************
 * Exact memoized program evaluation for the first authenticated genuine
 * case-10173 job.
 *
 * The expensive historical opcode-9 value is named by a closed selector from
 * the already proved typed calculation.  The memoized runner therefore only
 * evaluates the ordinary source instructions around that value.
 *****************************************************************************)
Theory compute_registeredCase10173GenuineProgramMemoEval
Ancestors
  compute_registeredCase10173HistProgramMemoEval
Libs
  bossLib preamble cv_transLib

Definition registered_case10173_genuine_center_boxes_def:
  registered_case10173_genuine_center_boxes =
    case registered_case10173_q_center_environment_positive
      registered_case10173_first_job_boxes of
    | NONE => Num 0
    | SOME center_boxes => center_boxes
End

Definition registered_case10173_genuine_hist_result_def:
  registered_case10173_genuine_hist_result =
    case bounded_historical_dihedral_first64_decimal
      registered_case10173_historical_center_environment_decimal
      registered_case10173_historical_center_root_delta
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_reciprocals of
    | NONE => Num 0
    | SOME (center_value,center_gradient) =>
      case bounded_historical_dihedral_second64_decimal
        registered_case10173_historical_box_environment_decimal
        registered_case10173_historical_box_root_delta
        registered_case10173_historical_box_root_four_x0
        registered_case10173_historical_box_reciprocals of
      | NONE => Num 0
      | SOME (box_value,box_gradient,hessian) =>
        case bounded_hessian64_rows hessian of
        | NONE => Num 0
        | SOME rows =>
          case bounded_object_fs_taylor_complete
            registered_case10173_historical_radii_words T
            center_value center_gradient hessian rows of
          | NONE => Num 0
          | SOME result => result
End

Definition registered_case10173_genuine_hist_item_def:
  registered_case10173_genuine_hist_item =
    Pair (Num 1) registered_case10173_genuine_hist_result
End

Definition registered_case10173_genuine_encoded_radii_def:
  registered_case10173_genuine_encoded_radii =
    registered_case10173_q_cv_list
      registered_case10173_historical_encoded_radii
End

Theorem registered_case10173_genuine_center_boxes_exact:
  registered_case10173_q_center_environment_positive
      registered_case10173_first_job_boxes =
    SOME registered_case10173_genuine_center_boxes
Proof
  mp_tac
    compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_source_inputs_exact
  >> strip_tac
  >> simp [registered_case10173_genuine_center_boxes_def]
QED

Theorem registered_case10173_genuine_hist_result_exact:
  ?center_value center_gradient box_value box_gradient hessian rows.
    bounded_historical_dihedral_first64_decimal
      registered_case10173_historical_center_environment_decimal
      registered_case10173_historical_center_root_delta
      registered_case10173_historical_center_root_four_x0
      registered_case10173_historical_center_reciprocals =
        SOME (center_value,center_gradient) /\
    bounded_historical_dihedral_second64_decimal
      registered_case10173_historical_box_environment_decimal
      registered_case10173_historical_box_root_delta
      registered_case10173_historical_box_root_four_x0
      registered_case10173_historical_box_reciprocals =
        SOME (box_value,box_gradient,hessian) /\
    bounded_hessian64_rows hessian = SOME rows /\
    bounded_object_fs_taylor_complete
      registered_case10173_historical_radii_words T
      center_value center_gradient hessian rows =
        SOME registered_case10173_genuine_hist_result
Proof
  mp_tac
    compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_historical_item_complete
  >> strip_tac
  >> qexists_tac `center_value`
  >> qexists_tac `center_gradient`
  >> qexists_tac `box_value`
  >> qexists_tac `box_gradient`
  >> qexists_tac `hessian`
  >> qexists_tac `rows`
  >> simp [registered_case10173_genuine_hist_result_def]
QED

Theorem registered_case10173_genuine_hist_item_eval_above_closed:
  registered_case10173_hist_item_eval_above 20000
    registered_case10173_genuine_center_boxes
    registered_case10173_first_job_boxes
    (registered_case10173_q_cv_list
      registered_case10173_historical_encoded_radii)
    registered_case10173_first_job_roots
    registered_case10173_genuine_hist_item
Proof
  mp_tac
    compute_registeredCase10173GenuineHistItemEvalTheory.registered_case10173_genuine_source_inputs_exact
  >> strip_tac
  >> fs [registered_case10173_genuine_center_boxes_exact]
  >> mp_tac registered_case10173_genuine_hist_result_exact
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_item_eval_above_def,
        registered_case10173_genuine_hist_item_def]
  >> rpt gen_tac
  >> strip_tac
  >> PURE_REWRITE_TAC
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> irule
       compute_registeredCase10173HistItemCompleteObjectEvalTheory.registered_case10173_hist_item_complete_object_eval
  >> `LENGTH center_gradient = 6` by
       (irule
          compute_registeredCase10173GenuineHistItemCallEvalTheory.registered_case10173_historical_center_gradient_length
        >> simp [])
  >> imp_res_tac
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_bounded_hessian64_rows_success_length
  >> conj_tac >- intLib.ARITH_TAC
  >> conj_tac
  >- (simp
        [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_def,
         compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >> qexists_tac
       `registered_case10173_historical_box_environment_decimal`
  >> qexists_tac `box_gradient`
  >> qexists_tac `box_value`
  >> qexists_tac
       `registered_case10173_historical_center_environment_decimal`
  >> qexists_tac `center_gradient`
  >> qexists_tac `center_value`
  >> qexists_tac `hessian`
  >> qexists_tac `registered_case10173_historical_radii_words`
  >> qexists_tac `rows`
  >> rpt conj_tac
  >- (simp
        [compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_decimal_def,
         compute_boundedCase10173JobBindingTheory.bounded_case10173_packet_box_environment_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- metis_tac []
  >- (simp
        [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_environment_decimal_def,
         compute_registeredCase10173RootInputsBindingTheory.bounded_case10173_packet_center_environment_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- metis_tac []
  >- (simp
        [compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_radii_words_def,
         compute_boundedCase10173DecimalInputBindingTheory.bounded_case10173_decimal_packet0_source_aligned_def,
         compute_boundedCase10173HistoricalCellDecimalDataTheory.bounded_case10173_decimal_packet0_def]
      >> intLib.ARITH_TAC)
  >- ACCEPT_TAC
       compute_registeredCase10173GenuineRadiusEvalTheory.registered_case10173_historical_encoded_radii_numerators
  >- simp []
  >- simp []
  >- (once_rewrite_tac
        [GSYM
          compute_registeredCase10173GenuineHistItemCallEvalTheory.registered_case10173_historical_center_environment_object_exact]
      >> mp_tac
           (Q.INST [`clock` |-> `clock - 3`]
             compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_first_order_exact_eval)
      >> impl_tac >- intLib.ARITH_TAC
      >> strip_tac
      >> qpat_x_assum
           `bounded_historical_dihedral_first64_decimal _ _ _
              registered_case10173_historical_center_reciprocals = _`
           (fn th =>
             assume_tac
               (REWRITE_RULE
                 [compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_historical_center_reciprocals_components]
                 th))
      >> gvs [])
  >> once_rewrite_tac
       [GSYM compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_environment_object_exact]
  >> irule
       compute_registeredCase10173HistoricalSecondOrderBoxEvalTheory.registered_case10173_historical_box_second_order_typed_eval
  >> simp []
  >> intLib.ARITH_TAC
QED

val registered_case10173_hist_program_run_memo_pre_def =
  cv_auto_trans_pre ""
    (compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_def
      |> measure_args [6]);

Theorem registered_case10173_hist_program_run_memo_pre[cv_pre]:
  !fuel center_boxes boxes radii roots item center_program box_program stack.
    registered_case10173_hist_program_run_memo_pre fuel
      center_boxes boxes radii roots item center_program box_program stack
Proof
  Induct_on `center_program`
  >- rw [Once registered_case10173_hist_program_run_memo_pre_def]
  >> rpt gen_tac
  >> Cases_on `box_program`
  >> rw [Once registered_case10173_hist_program_run_memo_pre_def]
  >> every_case_tac
  >> gvs []
QED

val _ = cv_trans
  compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_midpoint_positive_cv_def;
val _ = cv_trans
  compute_registeredCase10173CenterEnvironmentEvalTheory.registered_case10173_q_center_environment_positive_def;
val _ = cv_trans registered_case10173_genuine_center_boxes_def;
val registered_case10173_genuine_hist_result_value =
  time EVAL ``registered_case10173_genuine_hist_result``;
val _ = save_thm
  ("registered_case10173_genuine_hist_result_value",
   registered_case10173_genuine_hist_result_value);
val _ = cv_trans registered_case10173_genuine_hist_result_value;
val _ = cv_trans registered_case10173_genuine_hist_item_def;

val registered_case10173_genuine_encoded_radii_value =
  EVAL ``registered_case10173_genuine_encoded_radii``;
val _ = save_thm
  ("registered_case10173_genuine_encoded_radii_value",
   registered_case10173_genuine_encoded_radii_value);
val _ = cv_trans registered_case10173_genuine_encoded_radii_value;

val registered_case10173_genuine_spliced_center_program_value =
  EVAL ``registered_case10173_genuine_spliced_center_program``;
val _ = save_thm
  ("registered_case10173_genuine_spliced_center_program_value",
   registered_case10173_genuine_spliced_center_program_value);
val _ = cv_trans registered_case10173_genuine_spliced_center_program_value;

val registered_case10173_genuine_spliced_box_program_value =
  EVAL ``registered_case10173_genuine_spliced_box_program``;
val _ = save_thm
  ("registered_case10173_genuine_spliced_box_program_value",
   registered_case10173_genuine_spliced_box_program_value);
val _ = cv_trans registered_case10173_genuine_spliced_box_program_value;

val registered_case10173_genuine_program_memo_defined =
  time cv_eval
    ``IS_SOME
      (registered_case10173_hist_program_run_memo 100000
        registered_case10173_genuine_center_boxes
        registered_case10173_first_job_boxes
        registered_case10173_genuine_encoded_radii
        registered_case10173_first_job_roots
        registered_case10173_genuine_hist_item
        registered_case10173_genuine_spliced_center_program
        registered_case10173_genuine_spliced_box_program (Num 0))``;

val _ = save_thm
  ("registered_case10173_genuine_program_memo_defined",
   registered_case10173_genuine_program_memo_defined);

Theorem registered_case10173_genuine_program_memo_result:
  ?final_stack.
    registered_case10173_hist_program_run_memo 100000
      registered_case10173_genuine_center_boxes
      registered_case10173_first_job_boxes
      registered_case10173_genuine_encoded_radii
      registered_case10173_first_job_roots
      registered_case10173_genuine_hist_item
      registered_case10173_genuine_spliced_center_program
      registered_case10173_genuine_spliced_box_program (Num 0) =
    SOME final_stack
Proof
  mp_tac registered_case10173_genuine_program_memo_defined
  >> simp [IS_SOME_EXISTS]
QED

Theorem registered_case10173_genuine_program_run_eval:
  120098 < clock ==>
  ?final_stack.
    compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_case10173_hist_program_run»
        [from_cv registered_case10173_genuine_center_boxes;
         from_cv registered_case10173_first_job_boxes;
         from_cv registered_case10173_genuine_encoded_radii;
         from_cv registered_case10173_first_job_roots;
         from_cv registered_case10173_genuine_spliced_center_program;
         from_cv registered_case10173_genuine_spliced_box_program;
         from_cv (Num 0)])
      (refs:hol_refs) =
    (M_success (from_cv final_stack),refs)
Proof
  strip_tac
  >> mp_tac registered_case10173_genuine_program_memo_result
  >> strip_tac
  >> qexists_tac `final_stack`
  >> irule
       compute_registeredCase10173HistProgramMemoEvalTheory.registered_case10173_hist_program_run_memo_sound
  >> qexists_tac `100000`
  >> qexists_tac `registered_case10173_genuine_hist_item`
  >> qexists_tac `20000`
  >> simp
       [registered_case10173_genuine_encoded_radii_def,
        registered_case10173_genuine_hist_item_eval_above_closed,
        compute_registeredCase10173GenuineProgramDataTheory.registered_case10173_genuine_program_data_shape]
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
