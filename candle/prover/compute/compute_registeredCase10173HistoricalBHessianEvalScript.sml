(*****************************************************************************
 * Registered-source refinement for the historical b Hessian.
 *
 * The literal source keeps Hessians as six by six matrices while the bounded
 * checker keeps the symmetric upper triangle in 21 entries.  This theory
 * follows the literal entry/row construction and reconnects it to the compact
 * representation only at the typed boundary.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalBHessianEval
Ancestors
  compute_registeredCase10173HistoricalDeltaSecondEval
  compute_registeredCase10173HistoricalSecondOrderMatrixScaleEval
  compute_registeredCase10173HistoricalSqrtSecondEval
Libs
  bossLib preamble intLib

Theorem registered_case10173_fs_hist_scale2_typed_eval:
  bounded_historical_scale2 input = SOME twice /\
  5 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [Num 2;from_cv (bounded_interval64_object_cv input)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv twice)),refs)
Proof
  rpt strip_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalDeltaX4GradientEvalTheory.registered_case10173_fs_angle_interval_scale_object_eval)
  >> simp []
  >> irule
       compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_interval_scale_two_object_typed_exact
  >> simp []
QED

Theorem registered_case10173_fs_hist_gradient_correction_typed_eval:
  index < LENGTH gradient /\
  LENGTH gradient = 6 /\
  bounded_interval64_mul_decimal (EL index gradient) scalar =
      SOME correction /\
  15 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_lookup»
           [Num index;
            from_cv (bounded_interval64_object_cv_list gradient)];
         from_cv (bounded_interval64_object_cv scalar)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv correction)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv (EL index gradient)`
  >> qexists_tac `bounded_interval64_object_cv scalar`
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact,
        compute_execProofTheory.compute_eval_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_b_hessian_entry_rows_decimal_def:
  registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      rowindex colindex =
    let base = EL colindex (EL rowindex base_rows) in
    if rowindex = 0 then
      if colindex = 0 then
        case bounded_interval64_mul_decimal
          (EL 0 root_gradient) two_over_root_four of
        | NONE => NONE
        | SOME first_correction =>
          case bounded_historical_scale2 first_correction of
          | NONE => NONE
          | SOME twice_first_correction =>
            case bounded_interval64_mul_decimal
              root_delta two_over_root_four of
            | NONE => NONE
            | SOME diagonal_numerator =>
              case bounded_interval64_mul_decimal
                diagonal_numerator diagonal_reciprocal of
              | NONE => NONE
              | SOME diagonal_subtraction =>
                case bounded_interval64_add twice_first_correction
                  (bounded_interval64_neg diagonal_subtraction) of
                | NONE => NONE
                | SOME diagonal_correction =>
                    bounded_interval64_add base diagonal_correction
      else
        case bounded_interval64_mul_decimal
          (EL colindex root_gradient) two_over_root_four of
        | NONE => NONE
        | SOME correction => bounded_interval64_add base correction
    else if colindex = 0 then
      case bounded_interval64_mul_decimal
        (EL rowindex root_gradient) two_over_root_four of
      | NONE => NONE
      | SOME correction => bounded_interval64_add base correction
    else SOME base
End

Definition registered_case10173_fs_hist_b_hessian_entry_body_def:
  registered_case10173_fs_hist_b_hessian_entry_body =
    Let «base»
      (App «candle_cv_fs_angle_matrix_lookup»
        [Var «rowindex»;Var «colindex»;Var «base_hessian»])
      (If (Binop Eq (Var «rowindex») (Num 0))
        (If (Binop Eq (Var «colindex») (Num 0))
          (Let «twice_first_correction»
            (App «candle_cv_fs_angle_interval_scale»
              [Num 2;
               App «candle_cv_fs_angle_interval_mul»
                 [App «candle_cv_fs_interval_lookup»
                    [Num 0;Var «root_delta_gradient»];
                  Var «two_over_root_four_x0»]])
            (Let «diagonal_subtraction»
              (App «candle_cv_fs_angle_interval_mul»
                [App «candle_cv_fs_angle_interval_mul»
                   [Var «root_delta_value»;
                    Var «two_over_root_four_x0»];
                 App «candle_cv_fs_hist_positive_inv»
                   [App «candle_cv_fs_angle_interval_scale»
                      [Num 2;Var «x0»]]])
              (App «candle_cv_fs_interval_add»
                [Var «base»;
                 App «candle_cv_fs_interval_add»
                   [Var «twice_first_correction»;
                    App «candle_cv_fs_interval_neg»
                      [Var «diagonal_subtraction»]]])))
          (App «candle_cv_fs_interval_add»
            [Var «base»;
             App «candle_cv_fs_angle_interval_mul»
               [App «candle_cv_fs_interval_lookup»
                  [Var «colindex»;Var «root_delta_gradient»];
                Var «two_over_root_four_x0»]]))
        (If (Binop Eq (Var «colindex») (Num 0))
          (App «candle_cv_fs_interval_add»
            [Var «base»;
             App «candle_cv_fs_angle_interval_mul»
               [App «candle_cv_fs_interval_lookup»
                  [Var «rowindex»;Var «root_delta_gradient»];
                Var «two_over_root_four_x0»]])
          (Var «base»)))
End

Theorem registered_case10173_fs_hist_b_hessian_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_b_hessian_entry» =
    SOME
      ([«rowindex»;«colindex»;«base_hessian»;«root_delta_value»;
        «root_delta_gradient»;«two_over_root_four_x0»;«x0»],
       registered_case10173_fs_hist_b_hessian_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_b_hessian_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian_entry»
        [from_cv rowindex;from_cv colindex;from_cv base_hessian;
         from_cv root_delta_value;from_cv root_delta_gradient;
         from_cv two_over_root_four_x0;from_cv x0])
      (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);(«colindex»,from_cv colindex);
         («base_hessian»,from_cv base_hessian);
         («root_delta_value»,from_cv root_delta_value);
         («root_delta_gradient»,from_cv root_delta_gradient);
         («two_over_root_four_x0»,from_cv two_over_root_four_x0);
         («x0»,from_cv x0)]
        registered_case10173_fs_hist_b_hessian_entry_body) refs
Proof
  strip_tac
  >> irule
       compute_registeredCase10173HistProgramRunEvalTheory.registered_case10173_compute_eval_literal_app7
  >> simp [registered_case10173_fs_hist_b_hessian_entry_lookup]
QED

Theorem registered_case10173_fs_hist_scale2_gradient_correction_typed_eval:
  index < LENGTH gradient /\
  LENGTH gradient = 6 /\
  bounded_interval64_mul_decimal (EL index gradient) scalar =
      SOME correction /\
  bounded_historical_scale2 correction = SOME twice /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_scale»
        [Num 2;
         App «candle_cv_fs_angle_interval_mul»
           [App «candle_cv_fs_interval_lookup»
              [Num index;
               from_cv (bounded_interval64_object_cv_list gradient)];
            from_cv (bounded_interval64_object_cv scalar)]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv twice)),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_scale»
            [from_cv (Num 2);
             from_cv (bounded_interval64_object_cv correction)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app2_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> conj_tac
      >- simp
           [compute_evalTheory.compute_eval_def,
            compute_execTheory.from_cv_def,
            ml_monadBaseTheory.st_ex_return_def]
      >> irule registered_case10173_fs_hist_gradient_correction_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp [compute_execTheory.from_cv_def]
  >> irule registered_case10173_fs_hist_scale2_typed_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_diagonal_subtraction_typed_eval:
  bounded_interval64_mul_decimal root_delta two_over_root_four =
      SOME diagonal_numerator /\
  bounded_historical_scale2 x0 = SOME twice_x0 /\
  bounded_interval64_positive_inv_certificate_decimal
      twice_x0 diagonal_reciprocal /\
  bounded_interval64_mul_decimal diagonal_numerator diagonal_reciprocal =
      SOME diagonal_subtraction /\
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_angle_interval_mul»
           [from_cv (bounded_interval64_object_cv root_delta);
            from_cv (bounded_interval64_object_cv two_over_root_four)];
         App «candle_cv_fs_hist_positive_inv»
           [App «candle_cv_fs_angle_interval_scale»
              [Num 2;from_cv (bounded_interval64_object_cv x0)]]])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv diagonal_subtraction)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv diagonal_numerator`
  >> qexists_tac `bounded_interval64_object_cv diagonal_reciprocal`
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.registered_case10173_fs_hist_positive_inv_after_scale2_eval
  >> simp []
  >> qexists_tac `twice_x0`
  >> simp []
  >> irule
       compute_registeredCase10173HistoricalSqrtSecondEvalTheory.registered_case10173_interval_scale_two_object_typed_exact
  >> simp []
QED

Theorem registered_case10173_fs_hist_diagonal_correction_typed_eval:
  bounded_interval64_add twice_first_correction
      (bounded_interval64_neg diagonal_subtraction) =
      SOME diagonal_correction /\
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [from_cv (bounded_interval64_object_cv twice_first_correction);
         App «candle_cv_fs_interval_neg»
           [from_cv (bounded_interval64_object_cv diagonal_subtraction)]])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv diagonal_correction)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv twice_first_correction`
  >> qexists_tac
       `bounded_interval64_object_cv
          (bounded_interval64_neg diagonal_subtraction)`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact,
        compute_execProofTheory.compute_eval_from_cv]
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
QED

Theorem registered_case10173_b_hessian_entry_rows_diagonal_trace:
  registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      0 0 = SOME result ==>
  ?first_correction twice_first_correction diagonal_numerator
   diagonal_subtraction diagonal_correction.
    bounded_interval64_mul_decimal
      (EL 0 root_gradient) two_over_root_four = SOME first_correction /\
    bounded_historical_scale2 first_correction =
      SOME twice_first_correction /\
    bounded_interval64_mul_decimal root_delta two_over_root_four =
      SOME diagonal_numerator /\
    bounded_interval64_mul_decimal
      diagonal_numerator diagonal_reciprocal = SOME diagonal_subtraction /\
    bounded_interval64_add twice_first_correction
      (bounded_interval64_neg diagonal_subtraction) =
      SOME diagonal_correction /\
    bounded_interval64_add (EL 0 (EL 0 base_rows))
      diagonal_correction = SOME result
Proof
  simp [registered_case10173_b_hessian_entry_rows_decimal_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> metis_tac []
QED

Theorem registered_case10173_b_hessian_entry_rows_row0_trace:
  colindex <> 0 /\
  registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      0 colindex = SOME result ==>
  ?correction.
    bounded_interval64_mul_decimal
      (EL colindex root_gradient) two_over_root_four = SOME correction /\
    bounded_interval64_add (EL colindex (EL 0 base_rows)) correction =
      SOME result
Proof
  rpt strip_tac
  >> gvs [registered_case10173_b_hessian_entry_rows_decimal_def]
  >> Cases_on
       `bounded_interval64_mul_decimal
          (EL colindex root_gradient) two_over_root_four`
  >> gvs []
QED

Theorem registered_case10173_b_hessian_entry_rows_col0_trace:
  rowindex <> 0 /\
  registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      rowindex 0 = SOME result ==>
  ?correction.
    bounded_interval64_mul_decimal
      (EL rowindex root_gradient) two_over_root_four = SOME correction /\
    bounded_interval64_add (EL 0 (EL rowindex base_rows)) correction =
      SOME result
Proof
  rpt strip_tac
  >> gvs [registered_case10173_b_hessian_entry_rows_decimal_def]
  >> Cases_on
       `bounded_interval64_mul_decimal
          (EL rowindex root_gradient) two_over_root_four`
  >> gvs []
QED

Theorem registered_case10173_b_hessian_entry_rows_other_trace:
  rowindex <> 0 /\ colindex <> 0 /\
  registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      rowindex colindex = SOME result ==>
  result = EL colindex (EL rowindex base_rows)
Proof
  rpt strip_tac
  >> gvs [registered_case10173_b_hessian_entry_rows_decimal_def]
QED

Theorem registered_case10173_fs_hist_b_hessian_entry_rows_typed_eval:
  rowindex < 6 /\
  colindex < 6 /\
  LENGTH root_gradient = 6 /\
  LENGTH base_rows = 6 /\
  EVERY (\row. LENGTH row = 6) base_rows /\
  bounded_historical_scale2 x0 = SOME twice_x0 /\
  bounded_interval64_positive_inv_certificate_decimal
      twice_x0 diagonal_reciprocal /\
  registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      rowindex colindex = SOME result /\
  60 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian_entry»
        [from_cv (Num rowindex);from_cv (Num colindex);
         from_cv (bounded_interval64_object_cv_matrix base_rows);
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv_list root_gradient);
         from_cv (bounded_interval64_object_cv two_over_root_four);
         from_cv (bounded_interval64_object_cv x0)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> rw [registered_case10173_fs_hist_b_hessian_entry_unfold]
  >> simp
       [registered_case10173_fs_hist_b_hessian_entry_body_def,
        compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv
          (bounded_interval64_object_cv
            (EL colindex (EL rowindex base_rows)))`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_angle_matrix_lookup_typed_eval)
      >> fs [EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> Cases_on `rowindex = 0`
  >- (gvs []
      >> simp
           [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
      >> Cases_on `colindex = 0`
      >- (gvs []
          >> simp
               [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
                compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
          >> drule
               registered_case10173_b_hessian_entry_rows_diagonal_trace
          >> strip_tac
          >> irule
               compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac
               `from_cv
                 (bounded_interval64_object_cv twice_first_correction)`
          >> conj_tac
          >- (irule
                registered_case10173_fs_hist_scale2_gradient_correction_typed_eval
              >> simp []
              >> intLib.ARITH_TAC)
          >> simp
               [compute_evalTheory.subst_def,
                compute_execProofTheory.subst_from_cv]
          >> irule
               compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac
               `from_cv
                 (bounded_interval64_object_cv diagonal_subtraction)`
          >> conj_tac
          >- (irule
                registered_case10173_fs_hist_diagonal_subtraction_typed_eval
              >> conj_tac >- intLib.ARITH_TAC
              >> qexists_tac `diagonal_numerator`
              >> qexists_tac `diagonal_reciprocal`
              >> qexists_tac `twice_x0`
              >> simp [])
          >> simp
               [compute_evalTheory.subst_def,
                compute_execProofTheory.subst_from_cv]
          >> irule
               compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac
               `bounded_interval64_object_cv
                 (EL 0 (EL 0 base_rows))`
          >> qexists_tac
               `bounded_interval64_object_cv diagonal_correction`
          >> simp
               [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact,
                compute_execProofTheory.compute_eval_from_cv]
          >> irule
               registered_case10173_fs_hist_diagonal_correction_typed_eval
          >> simp []
          >> intLib.ARITH_TAC)
      >> simp
           [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
            compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
      >> imp_res_tac registered_case10173_b_hessian_entry_rows_row0_trace
      >> gvs []
      >> irule
           compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `bounded_interval64_object_cv
             (EL colindex (EL 0 base_rows))`
      >> qexists_tac `bounded_interval64_object_cv correction`
      >> simp
           [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact,
            compute_execProofTheory.compute_eval_from_cv]
      >> irule registered_case10173_fs_hist_gradient_correction_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> Cases_on `colindex = 0`
  >- (gvs []
      >> simp
           [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
      >> imp_res_tac registered_case10173_b_hessian_entry_rows_col0_trace
      >> gvs []
      >> irule
           compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac
           `bounded_interval64_object_cv
             (EL 0 (EL rowindex base_rows))`
      >> qexists_tac `bounded_interval64_object_cv correction`
      >> simp
           [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact,
            compute_execProofTheory.compute_eval_from_cv]
      >> irule registered_case10173_fs_hist_gradient_correction_typed_eval
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
        compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> imp_res_tac registered_case10173_b_hessian_entry_rows_other_trace
  >> gvs [compute_execProofTheory.compute_eval_from_cv]
QED

Definition registered_case10173_b_hessian_row_rows_decimal_def:
  registered_case10173_b_hessian_row_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      rowindex =
    case registered_case10173_b_hessian_entry_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows
      rowindex 0 of
    | NONE => NONE
    | SOME r0 =>
      case registered_case10173_b_hessian_entry_rows_decimal root_delta
        two_over_root_four diagonal_reciprocal root_gradient base_rows
        rowindex 1 of
      | NONE => NONE
      | SOME r1 =>
        case registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 2 of
        | NONE => NONE
        | SOME r2 =>
          case registered_case10173_b_hessian_entry_rows_decimal root_delta
            two_over_root_four diagonal_reciprocal root_gradient base_rows
            rowindex 3 of
          | NONE => NONE
          | SOME r3 =>
            case registered_case10173_b_hessian_entry_rows_decimal root_delta
              two_over_root_four diagonal_reciprocal root_gradient base_rows
              rowindex 4 of
            | NONE => NONE
            | SOME r4 =>
              case registered_case10173_b_hessian_entry_rows_decimal root_delta
                two_over_root_four diagonal_reciprocal root_gradient base_rows
                rowindex 5 of
              | NONE => NONE
              | SOME r5 => SOME [r0;r1;r2;r3;r4;r5]
End

Definition registered_case10173_fs_hist_b_hessian_row_body_def:
  registered_case10173_fs_hist_b_hessian_row_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_hist_b_hessian_entry»
         [Var «rowindex»;Num 0;Var «base_hessian»;
          Var «root_delta_value»;Var «root_delta_gradient»;
          Var «two_over_root_four_x0»;Var «x0»];
       App «candle_cv_fs_hist_b_hessian_entry»
         [Var «rowindex»;Num 1;Var «base_hessian»;
          Var «root_delta_value»;Var «root_delta_gradient»;
          Var «two_over_root_four_x0»;Var «x0»];
       App «candle_cv_fs_hist_b_hessian_entry»
         [Var «rowindex»;Num 2;Var «base_hessian»;
          Var «root_delta_value»;Var «root_delta_gradient»;
          Var «two_over_root_four_x0»;Var «x0»];
       App «candle_cv_fs_hist_b_hessian_entry»
         [Var «rowindex»;Num 3;Var «base_hessian»;
          Var «root_delta_value»;Var «root_delta_gradient»;
          Var «two_over_root_four_x0»;Var «x0»];
       App «candle_cv_fs_hist_b_hessian_entry»
         [Var «rowindex»;Num 4;Var «base_hessian»;
          Var «root_delta_value»;Var «root_delta_gradient»;
          Var «two_over_root_four_x0»;Var «x0»];
       App «candle_cv_fs_hist_b_hessian_entry»
         [Var «rowindex»;Num 5;Var «base_hessian»;
          Var «root_delta_value»;Var «root_delta_gradient»;
          Var «two_over_root_four_x0»;Var «x0»]]
End

Theorem registered_case10173_fs_hist_b_hessian_row_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_b_hessian_row» =
    SOME
      ([«rowindex»;«base_hessian»;«root_delta_value»;
        «root_delta_gradient»;«two_over_root_four_x0»;«x0»],
       registered_case10173_fs_hist_b_hessian_row_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_b_hessian_row_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian_row»
        [from_cv rowindex;from_cv base_hessian;
         from_cv root_delta_value;from_cv root_delta_gradient;
         from_cv two_over_root_four_x0;from_cv x0]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);
         («base_hessian»,from_cv base_hessian);
         («root_delta_value»,from_cv root_delta_value);
         («root_delta_gradient»,from_cv root_delta_gradient);
         («two_over_root_four_x0»,from_cv two_over_root_four_x0);
         («x0»,from_cv x0)]
        registered_case10173_fs_hist_b_hessian_row_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_b_hessian_row_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_b_hessian_row_typed_eval:
  rowindex < 6 /\
  LENGTH root_gradient = 6 /\
  LENGTH base_rows = 6 /\
  EVERY (\row. LENGTH row = 6) base_rows /\
  bounded_historical_scale2 x0 = SOME twice_x0 /\
  bounded_interval64_positive_inv_certificate_decimal twice_x0
    diagonal_reciprocal /\
  registered_case10173_b_hessian_row_rows_decimal root_delta
    two_over_root_four diagonal_reciprocal root_gradient base_rows
    rowindex = SOME result /\
  62 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian_row»
        [from_cv (Num rowindex);
         from_cv (bounded_interval64_object_cv_matrix base_rows);
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv_list root_gradient);
         from_cv (bounded_interval64_object_cv two_over_root_four);
         from_cv (bounded_interval64_object_cv x0)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_b_hessian_row_unfold]
  >> simp
       [registered_case10173_fs_hist_b_hessian_row_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 0`
  >> gvs [registered_case10173_b_hessian_row_rows_decimal_def]
  >> Cases_on
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 1`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 2`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 3`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 4`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 5`
  >> gvs []
  >> rename1
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 0 = SOME r0`
  >> rename1
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 1 = SOME r1`
  >> rename1
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 2 = SOME r2`
  >> rename1
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 3 = SOME r3`
  >> rename1
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 4 = SOME r4`
  >> rename1
       `registered_case10173_b_hessian_entry_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows
          rowindex 5 = SOME r5`
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv (bounded_interval64_object_cv r0);
             from_cv (bounded_interval64_object_cv r1);
             from_cv (bounded_interval64_object_cv r2);
             from_cv (bounded_interval64_object_cv r3);
             from_cv (bounded_interval64_object_cv r4);
             from_cv (bounded_interval64_object_cv r5)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_b_hessian_entry_rows_typed_eval)
      >> simp []
      >> qexists_tac `diagonal_reciprocal`
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
          compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval)
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_b_hessian_rows_decimal_def:
  registered_case10173_b_hessian_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows =
    case registered_case10173_b_hessian_row_rows_decimal root_delta
      two_over_root_four diagonal_reciprocal root_gradient base_rows 0 of
    | NONE => NONE
    | SOME r0 =>
      case registered_case10173_b_hessian_row_rows_decimal root_delta
        two_over_root_four diagonal_reciprocal root_gradient base_rows 1 of
      | NONE => NONE
      | SOME r1 =>
        case registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 2 of
        | NONE => NONE
        | SOME r2 =>
          case registered_case10173_b_hessian_row_rows_decimal root_delta
            two_over_root_four diagonal_reciprocal root_gradient base_rows 3 of
          | NONE => NONE
          | SOME r3 =>
            case registered_case10173_b_hessian_row_rows_decimal root_delta
              two_over_root_four diagonal_reciprocal root_gradient base_rows 4 of
            | NONE => NONE
            | SOME r4 =>
              case registered_case10173_b_hessian_row_rows_decimal root_delta
                two_over_root_four diagonal_reciprocal root_gradient base_rows 5 of
              | NONE => NONE
              | SOME r5 => SOME [r0;r1;r2;r3;r4;r5]
End

Definition registered_case10173_fs_hist_b_hessian_body_def:
  registered_case10173_fs_hist_b_hessian_body =
    Let «base_hessian»
      (App «candle_cv_fs_hist_matrix_scale»
        [Var «root_four_x0»;Var «root_delta_hessian»])
      (App «candle_cv_fs_angle_six»
        [App «candle_cv_fs_hist_b_hessian_row»
           [Num 0;Var «base_hessian»;Var «root_delta_value»;
            Var «root_delta_gradient»;Var «two_over_root_four_x0»;Var «x0»];
         App «candle_cv_fs_hist_b_hessian_row»
           [Num 1;Var «base_hessian»;Var «root_delta_value»;
            Var «root_delta_gradient»;Var «two_over_root_four_x0»;Var «x0»];
         App «candle_cv_fs_hist_b_hessian_row»
           [Num 2;Var «base_hessian»;Var «root_delta_value»;
            Var «root_delta_gradient»;Var «two_over_root_four_x0»;Var «x0»];
         App «candle_cv_fs_hist_b_hessian_row»
           [Num 3;Var «base_hessian»;Var «root_delta_value»;
            Var «root_delta_gradient»;Var «two_over_root_four_x0»;Var «x0»];
         App «candle_cv_fs_hist_b_hessian_row»
           [Num 4;Var «base_hessian»;Var «root_delta_value»;
            Var «root_delta_gradient»;Var «two_over_root_four_x0»;Var «x0»];
         App «candle_cv_fs_hist_b_hessian_row»
           [Num 5;Var «base_hessian»;Var «root_delta_value»;
            Var «root_delta_gradient»;Var «two_over_root_four_x0»;Var «x0»]])
End

Theorem registered_case10173_fs_hist_b_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_b_hessian» =
    SOME
      ([«root_four_x0»;«root_delta_value»;«root_delta_gradient»;
        «root_delta_hessian»;«two_over_root_four_x0»;«x0»],
       registered_case10173_fs_hist_b_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_b_hessian_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian»
        [from_cv root_four_x0;from_cv root_delta_value;
         from_cv root_delta_gradient;from_cv root_delta_hessian;
         from_cv two_over_root_four_x0;from_cv x0]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«root_four_x0»,from_cv root_four_x0);
         («root_delta_value»,from_cv root_delta_value);
         («root_delta_gradient»,from_cv root_delta_gradient);
         («root_delta_hessian»,from_cv root_delta_hessian);
         («two_over_root_four_x0»,from_cv two_over_root_four_x0);
         («x0»,from_cv x0)]
        registered_case10173_fs_hist_b_hessian_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_b_hessian_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_b_hessian_typed_eval:
  LENGTH root_gradient = 6 /\
  LENGTH root_hessian_rows = 6 /\
  EVERY (\row. LENGTH row = 6) root_hessian_rows /\
  bounded_interval64_matrix_scale_decimal root_four root_hessian_rows =
    SOME base_rows /\
  LENGTH base_rows = 6 /\
  EVERY (\row. LENGTH row = 6) base_rows /\
  bounded_historical_scale2 x0 = SOME twice_x0 /\
  bounded_interval64_positive_inv_certificate_decimal twice_x0
    diagonal_reciprocal /\
  registered_case10173_b_hessian_rows_decimal root_delta
    two_over_root_four diagonal_reciprocal root_gradient base_rows =
    SOME result_rows /\
  SUM (MAP LENGTH root_hessian_rows) + LENGTH root_hessian_rows + 12 <
    clock - 1 /\
  64 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_b_hessian»
        [from_cv (bounded_interval64_object_cv root_four);
         from_cv (bounded_interval64_object_cv root_delta);
         from_cv (bounded_interval64_object_cv_list root_gradient);
         from_cv
           (bounded_interval64_object_cv_matrix root_hessian_rows);
         from_cv (bounded_interval64_object_cv two_over_root_four);
         from_cv (bounded_interval64_object_cv x0)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix result_rows)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_b_hessian_unfold]
  >> simp
       [registered_case10173_fs_hist_b_hessian_body_def,
        compute_evalTheory.subst_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac
       `from_cv (bounded_interval64_object_cv_matrix base_rows)`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalSecondOrderMatrixScaleEvalTheory.registered_case10173_fs_hist_matrix_scale_typed_eval
      >> simp [])
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> Cases_on
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 0`
  >> gvs [registered_case10173_b_hessian_rows_decimal_def]
  >> Cases_on
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 1`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 2`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 3`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 4`
  >> gvs []
  >> Cases_on
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 5`
  >> gvs []
  >> rename1
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 0 =
        SOME r0`
  >> rename1
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 1 =
        SOME r1`
  >> rename1
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 2 =
        SOME r2`
  >> rename1
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 3 =
        SOME r3`
  >> rename1
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 4 =
        SOME r4`
  >> rename1
       `registered_case10173_b_hessian_row_rows_decimal root_delta
          two_over_root_four diagonal_reciprocal root_gradient base_rows 5 =
        SOME r5`
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 2)
          registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_six»
            [from_cv (bounded_interval64_object_cv_list r0);
             from_cv (bounded_interval64_object_cv_list r1);
             from_cv (bounded_interval64_object_cv_list r2);
             from_cv (bounded_interval64_object_cv_list r3);
             from_cv (bounded_interval64_object_cv_list r4);
             from_cv (bounded_interval64_object_cv_list r5)]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalCombinatorEvalTheory.registered_case10173_compute_eval_app6_argument_results
      >> simp []
      >> rpt conj_tac
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_b_hessian_row_typed_eval)
      >> simp []
      >> qexists_tac `diagonal_reciprocal`
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_boundedObjectTaylorCompleteDecimalTheory.bounded_interval64_object_cv_matrix_def,
        compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def]
  >> irule
       (SIMP_RULE std_ss
         [compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_cv_list_def,
          compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_six_eval)
  >> intLib.ARITH_TAC
QED

val _ = export_theory ();
