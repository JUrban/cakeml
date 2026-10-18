(*****************************************************************************
 * Registered-source refinement for the historical final dihedral Hessian.
 *
 * The literal source materializes a symmetric six-by-six matrix.  The typed
 * numerical model retains the 21 upper-triangular entries, so this theory
 * first states the exact row algorithm and connects it to that compact
 * semantic result.  Source-evaluator lemmas are layered on this definition.
 *****************************************************************************)
Theory compute_registeredCase10173HistoricalFinalHessianEval
Ancestors
  compute_registeredCase10173HistoricalLogUGradientEval
Libs
  bossLib preamble intLib

Definition registered_case10173_final_hessian_entry_rows_decimal_def:
  registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
      reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
      result_gradient logarithmic_u_gradient rowindex colindex =
    case bounded_interval64_mul_decimal b
      (EL colindex (EL rowindex delta_x4_rows)) of
    | NONE => NONE
    | SOME first_term =>
      let common_first = bounded_interval64_neg first_term in
      case bounded_interval64_mul_decimal delta_x4
        (EL colindex (EL rowindex b_rows)) of
      | NONE => NONE
      | SOME common_last =>
        case
          (if rowindex = colindex then
             bounded_interval64_add common_first common_last
           else
             case bounded_interval64_mul_decimal
               (EL rowindex delta_x4_gradient) (EL colindex b_gradient) of
             | NONE => NONE
             | SOME second_term =>
               case bounded_interval64_mul_decimal
                 (EL colindex delta_x4_gradient) (EL rowindex b_gradient) of
               | NONE => NONE
               | SOME third_term =>
                   bounded_interval64_sum
                     [common_first;bounded_interval64_neg second_term;
                      third_term;common_last]) of
        | NONE => NONE
        | SOME identity =>
          case bounded_interval64_mul_decimal reciprocal_u identity of
          | NONE => NONE
          | SOME scaled_identity =>
            case bounded_interval64_mul_decimal
              (EL rowindex result_gradient)
              (EL colindex logarithmic_u_gradient) of
            | NONE => NONE
            | SOME logarithmic_term =>
                bounded_interval64_add scaled_identity
                  (bounded_interval64_neg logarithmic_term)
End

Definition registered_case10173_final_hessian_symmetric_entry_rows_decimal_def:
  registered_case10173_final_hessian_symmetric_entry_rows_decimal delta_x4 b
      reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
      result_gradient logarithmic_u_gradient rowindex colindex =
    if colindex < rowindex then
      registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
        reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
        result_gradient logarithmic_u_gradient colindex rowindex
    else
      registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
        reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
        result_gradient logarithmic_u_gradient rowindex colindex
End

Definition registered_case10173_final_hessian_row_rows_decimal_def:
  registered_case10173_final_hessian_row_rows_decimal delta_x4 b reciprocal_u
      delta_x4_gradient delta_x4_rows b_gradient b_rows result_gradient
      logarithmic_u_gradient rowindex =
    case registered_case10173_final_hessian_symmetric_entry_rows_decimal
      delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows b_gradient
      b_rows result_gradient logarithmic_u_gradient rowindex 0 of
    | NONE => NONE
    | SOME r0 =>
      case registered_case10173_final_hessian_symmetric_entry_rows_decimal
        delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows b_gradient
        b_rows result_gradient logarithmic_u_gradient rowindex 1 of
      | NONE => NONE
      | SOME r1 =>
        case registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows b_gradient
          b_rows result_gradient logarithmic_u_gradient rowindex 2 of
        | NONE => NONE
        | SOME r2 =>
          case registered_case10173_final_hessian_symmetric_entry_rows_decimal
            delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows b_gradient
            b_rows result_gradient logarithmic_u_gradient rowindex 3 of
          | NONE => NONE
          | SOME r3 =>
            case registered_case10173_final_hessian_symmetric_entry_rows_decimal
              delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
              b_gradient b_rows result_gradient logarithmic_u_gradient
              rowindex 4 of
            | NONE => NONE
            | SOME r4 =>
              case registered_case10173_final_hessian_symmetric_entry_rows_decimal
                delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
                b_gradient b_rows result_gradient logarithmic_u_gradient
                rowindex 5 of
              | NONE => NONE
              | SOME r5 => SOME [r0;r1;r2;r3;r4;r5]
End

Definition registered_case10173_final_hessian_rows_decimal_def:
  registered_case10173_final_hessian_rows_decimal delta_x4 b reciprocal_u
      delta_x4_gradient delta_x4_rows b_gradient b_rows result_gradient
      logarithmic_u_gradient =
    case registered_case10173_final_hessian_row_rows_decimal delta_x4 b
      reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
      result_gradient logarithmic_u_gradient 0 of
    | NONE => NONE
    | SOME r0 =>
      case registered_case10173_final_hessian_row_rows_decimal delta_x4 b
        reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
        result_gradient logarithmic_u_gradient 1 of
      | NONE => NONE
      | SOME r1 =>
        case registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 2 of
        | NONE => NONE
        | SOME r2 =>
          case registered_case10173_final_hessian_row_rows_decimal delta_x4 b
            reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
            result_gradient logarithmic_u_gradient 3 of
          | NONE => NONE
          | SOME r3 =>
            case registered_case10173_final_hessian_row_rows_decimal delta_x4 b
              reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
              result_gradient logarithmic_u_gradient 4 of
            | NONE => NONE
            | SOME r4 =>
              case registered_case10173_final_hessian_row_rows_decimal
                delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
                b_gradient b_rows result_gradient logarithmic_u_gradient 5 of
              | NONE => NONE
              | SOME r5 => SOME [r0;r1;r2;r3;r4;r5]
End

Theorem registered_case10173_bounded_interval64_nth_el:
  !values index.
    index < LENGTH values ==>
    bounded_interval64_nth values index = SOME (EL index values)
Proof
  Induct
  >> Cases_on `index`
  >> simp [compute_boundedTaylorBaseTheory.bounded_interval64_nth_def]
QED

Theorem registered_case10173_final_hessian_entry_rows_semantic:
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  rowindex < 6 /\ colindex < 6 ==>
  registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
    reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
    result_gradient logarithmic_u_gradient rowindex colindex =
  bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
    delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
    rowindex colindex (EL colindex (EL rowindex delta_x4_rows))
    (EL colindex (EL rowindex b_rows))
Proof
  rpt strip_tac
  >> simp
       [registered_case10173_final_hessian_entry_rows_decimal_def,
        compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_entry_decimal_def,
        registered_case10173_bounded_interval64_nth_el]
QED

Theorem registered_case10173_final_hessian_compact_source_trace:
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
    delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
    bounded_delta64_hessian_indices
    [d00;d01;d02;d03;d04;d05;d11;d12;d13;d14;d15;
     d22;d23;d24;d25;d33;d34;d35;d44;d45;d55]
    [b00;b01;b02;b03;b04;b05;b11;b12;b13;b14;b15;
     b22;b23;b24;b25;b33;b34;b35;b44;b45;b55] = SOME result ==>
  ?r00 r01 r02 r03 r04 r05 r11 r12 r13 r14 r15
   r22 r23 r24 r25 r33 r34 r35 r44 r45 r55.
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      0 0 d00 b00 = SOME r00 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      0 1 d01 b01 = SOME r01 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      0 2 d02 b02 = SOME r02 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      0 3 d03 b03 = SOME r03 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      0 4 d04 b04 = SOME r04 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      0 5 d05 b05 = SOME r05 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      1 1 d11 b11 = SOME r11 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      1 2 d12 b12 = SOME r12 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      1 3 d13 b13 = SOME r13 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      1 4 d14 b14 = SOME r14 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      1 5 d15 b15 = SOME r15 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      2 2 d22 b22 = SOME r22 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      2 3 d23 b23 = SOME r23 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      2 4 d24 b24 = SOME r24 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      2 5 d25 b25 = SOME r25 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      3 3 d33 b33 = SOME r33 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      3 4 d34 b34 = SOME r34 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      3 5 d35 b35 = SOME r35 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      4 4 d44 b44 = SOME r44 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      4 5 d45 b45 = SOME r45 /\
    bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      5 5 d55 b55 = SOME r55 /\
    result =
      [r00;r01;r02;r03;r04;r05;r11;r12;r13;r14;r15;
       r22;r23;r24;r25;r33;r34;r35;r44;r45;r55]
Proof
  simp
    [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def,
     compute_boundedHistoricalDihedralSecondDecimalTheory.bounded_historical_second_hessian_decimal_def]
  >> TOP_CASE_TAC >> gvs []
  >> TOP_CASE_TAC >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 0 1 d01 b01` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 0 2 d02 b02` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 0 3 d03 b03` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 0 4 d04 b04` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 0 5 d05 b05` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 1 1 d11 b11` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 1 2 d12 b12` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 1 3 d13 b13` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 1 4 d14 b14` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 1 5 d15 b15` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 2 2 d22 b22` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 2 3 d23 b23` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 2 4 d24 b24` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 2 5 d25 b25` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 3 3 d33 b33` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 3 4 d34 b34` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 3 5 d35 b35` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 4 4 d44 b44` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 4 5 d45 b45` >> gvs []
  >> Cases_on
       `bounded_historical_second_hessian_entry_decimal delta_x4 b
          reciprocal_u delta_x4_gradient b_gradient result_gradient
          logarithmic_u_gradient 5 5 d55 b55` >> gvs []
QED

Theorem registered_case10173_final_hessian_rows_decimal_compact:
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  bounded_hessian64_rows delta_x4_hessian = SOME delta_x4_rows /\
  bounded_hessian64_rows b_hessian = SOME b_rows /\
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
    delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
    bounded_delta64_hessian_indices delta_x4_hessian b_hessian =
    SOME result_hessian /\
  bounded_hessian64_rows result_hessian = SOME result_rows ==>
  registered_case10173_final_hessian_rows_decimal delta_x4 b reciprocal_u
    delta_x4_gradient delta_x4_rows b_gradient b_rows result_gradient
    logarithmic_u_gradient = SOME result_rows
Proof
  rpt strip_tac
  >> imp_res_tac
       compute_registeredCase10173HistoricalFirstOrderCenterEvalTheory.length_six_cases
  >> gvs []
  >> fs
       [compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> rpt (pop_assum mp_tac)
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> rpt strip_tac
  >> gvs []
  >> drule registered_case10173_final_hessian_compact_source_trace
  >> strip_tac
  >> gvs []
  >> fs
       [registered_case10173_final_hessian_rows_decimal_def,
        registered_case10173_final_hessian_row_rows_decimal_def,
        registered_case10173_final_hessian_symmetric_entry_rows_decimal_def,
        registered_case10173_final_hessian_entry_rows_semantic]
QED

Theorem registered_case10173_final_hessian_entry_diagonal_trace:
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  rowindex < 6 /\ colindex < 6 /\ rowindex = colindex /\
  registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
    reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
    result_gradient logarithmic_u_gradient rowindex colindex = SOME result ==>
  ?first_term common_last identity scaled_identity logarithmic_term.
    bounded_interval64_mul_decimal b
      (EL colindex (EL rowindex delta_x4_rows)) = SOME first_term /\
    bounded_interval64_mul_decimal delta_x4
      (EL colindex (EL rowindex b_rows)) = SOME common_last /\
    bounded_interval64_add (bounded_interval64_neg first_term) common_last =
      SOME identity /\
    bounded_interval64_mul_decimal reciprocal_u identity =
      SOME scaled_identity /\
    bounded_interval64_mul_decimal (EL rowindex result_gradient)
      (EL colindex logarithmic_u_gradient) = SOME logarithmic_term /\
    bounded_interval64_add scaled_identity
      (bounded_interval64_neg logarithmic_term) = SOME result
Proof
  rpt strip_tac
  >> gvs [registered_case10173_final_hessian_entry_rows_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem registered_case10173_final_hessian_entry_offdiagonal_trace:
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  rowindex < 6 /\ colindex < 6 /\ rowindex <> colindex /\
  registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
    reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
    result_gradient logarithmic_u_gradient rowindex colindex = SOME result ==>
  ?first_term common_last second_term third_term identity scaled_identity
   logarithmic_term.
    bounded_interval64_mul_decimal b
      (EL colindex (EL rowindex delta_x4_rows)) = SOME first_term /\
    bounded_interval64_mul_decimal delta_x4
      (EL colindex (EL rowindex b_rows)) = SOME common_last /\
    bounded_interval64_mul_decimal (EL rowindex delta_x4_gradient)
      (EL colindex b_gradient) = SOME second_term /\
    bounded_interval64_mul_decimal (EL colindex delta_x4_gradient)
      (EL rowindex b_gradient) = SOME third_term /\
    bounded_interval64_sum
      [bounded_interval64_neg first_term;
       bounded_interval64_neg second_term;third_term;common_last] =
      SOME identity /\
    bounded_interval64_mul_decimal reciprocal_u identity =
      SOME scaled_identity /\
    bounded_interval64_mul_decimal (EL rowindex result_gradient)
      (EL colindex logarithmic_u_gradient) = SOME logarithmic_term /\
    bounded_interval64_add scaled_identity
      (bounded_interval64_neg logarithmic_term) = SOME result
Proof
  rpt strip_tac
  >> gvs [registered_case10173_final_hessian_entry_rows_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Definition registered_case10173_fs_hist_final_hessian_entry_body_def:
  registered_case10173_fs_hist_final_hessian_entry_body =
    Let «common_first»
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_angle_interval_mul»
          [Var «b»;
           App «candle_cv_fs_angle_matrix_lookup»
             [Var «rowindex»;Var «colindex»;Var «delta_x4_hessian»]]])
      (Let «common_last»
        (App «candle_cv_fs_angle_interval_mul»
          [Var «delta_x4_value»;
           App «candle_cv_fs_angle_matrix_lookup»
             [Var «rowindex»;Var «colindex»;Var «b_hessian»]])
        (Let «identity»
          (If (Binop Eq (Var «rowindex») (Var «colindex»))
            (App «candle_cv_fs_interval_add»
              [Var «common_first»;Var «common_last»])
            (App «candle_cv_fs_angle_interval_sum»
              [App «candle_cv_fs_hist_four»
                [Var «common_first»;
                 App «candle_cv_fs_interval_neg»
                   [App «candle_cv_fs_angle_interval_mul»
                     [App «candle_cv_fs_interval_lookup»
                        [Var «rowindex»;Var «delta_x4_gradient»];
                      App «candle_cv_fs_interval_lookup»
                        [Var «colindex»;Var «b_gradient»]]];
                 App «candle_cv_fs_angle_interval_mul»
                   [App «candle_cv_fs_interval_lookup»
                      [Var «colindex»;Var «delta_x4_gradient»];
                    App «candle_cv_fs_interval_lookup»
                      [Var «rowindex»;Var «b_gradient»]];
                 Var «common_last»]]))
          (App «candle_cv_fs_interval_add»
            [App «candle_cv_fs_angle_interval_mul»
               [Var «reciprocal_u»;Var «identity»];
             App «candle_cv_fs_interval_neg»
               [App «candle_cv_fs_angle_interval_mul»
                 [App «candle_cv_fs_interval_lookup»
                    [Var «rowindex»;Var «result_gradient»];
                  App «candle_cv_fs_interval_lookup»
                    [Var «colindex»;Var «log_u_gradient»]]]])))
End

Theorem registered_case10173_fs_hist_final_hessian_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_final_hessian_entry» =
    SOME
      ([«rowindex»;«colindex»;«b»;«delta_x4_value»;
        «delta_x4_gradient»;«delta_x4_hessian»;«b_gradient»;«b_hessian»;
        «reciprocal_u»;«result_gradient»;«log_u_gradient»],
       registered_case10173_fs_hist_final_hessian_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian_entry»
        [from_cv rowindex;from_cv colindex;from_cv b;from_cv delta_x4_value;
         from_cv delta_x4_gradient;from_cv delta_x4_hessian;
         from_cv b_gradient;from_cv b_hessian;from_cv reciprocal_u;
         from_cv result_gradient;from_cv log_u_gradient]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);(«colindex»,from_cv colindex);
         («b»,from_cv b);(«delta_x4_value»,from_cv delta_x4_value);
         («delta_x4_gradient»,from_cv delta_x4_gradient);
         («delta_x4_hessian»,from_cv delta_x4_hessian);
         («b_gradient»,from_cv b_gradient);(«b_hessian»,from_cv b_hessian);
         («reciprocal_u»,from_cv reciprocal_u);
         («result_gradient»,from_cv result_gradient);
         («log_u_gradient»,from_cv log_u_gradient)]
        registered_case10173_fs_hist_final_hessian_entry_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_final_hessian_entry_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_interval_neg_argument_result:
  bounded_object_fs_interval_neg source = SOME result /\
  4 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      source_expression (refs:hol_refs) =
    (M_success (from_cv source),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_neg» [source_expression]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_interval_neg» [from_cv source]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> simp [])
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_neg_eval
  >> simp []
QED

Theorem registered_case10173_fs_hist_mul_matrix_lookup_typed_eval:
  rowindex < 6 /\ colindex < 6 /\
  rowindex < LENGTH rows /\
  colindex < LENGTH (EL rowindex rows) /\
  bounded_interval64_mul_decimal scalar (EL colindex (EL rowindex rows)) =
    SOME result /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [from_cv (bounded_interval64_object_cv scalar);
         App «candle_cv_fs_angle_matrix_lookup»
           [from_cv (Num rowindex);from_cv (Num colindex);
            from_cv (bounded_interval64_object_cv_matrix rows)]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv scalar`
  >> qexists_tac
       `bounded_interval64_object_cv (EL colindex (EL rowindex rows))`
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact,
        compute_execProofTheory.compute_eval_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalSecondOrderPrimitiveEvalTheory.registered_case10173_fs_angle_matrix_lookup_typed_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_mul_list_lookups_typed_eval:
  leftindex < 6 /\ rightindex < 6 /\
  leftindex < LENGTH left /\
  rightindex < LENGTH right /\
  bounded_interval64_mul_decimal (EL leftindex left) (EL rightindex right) =
    SOME result /\
  20 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_mul»
        [App «candle_cv_fs_interval_lookup»
           [from_cv (Num leftindex);
            from_cv (bounded_interval64_object_cv_list left)];
         App «candle_cv_fs_interval_lookup»
           [from_cv (Num rightindex);
            from_cv (bounded_interval64_object_cv_list right)]])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_angle_interval_mul_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv (EL leftindex left)`
  >> qexists_tac `bounded_interval64_object_cv (EL rightindex right)`
  >> simp
       [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
  >> conj_tac
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_lookup_object_list_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_interval_sum_object_four_typed_exact:
  bounded_interval64_sum [r0;r1;r2;r3] = SOME result ==>
  registered_case10173_fs_interval_sum_object
    [bounded_interval64_object_cv r0;bounded_interval64_object_cv r1;
     bounded_interval64_object_cv r2;bounded_interval64_object_cv r3] =
    SOME (bounded_interval64_object_cv result)
Proof
  strip_tac
  >> mp_tac
       (Q.INST
         [`value` |-> `r0`,`values` |-> `[r1;r2;r3]`,
          `result` |-> `result`]
         compute_registeredCase10173HistoricalDeltaX4ValueBlockEvalTheory.registered_case10173_interval_sum_object_typed_exact)
  >> simp [listTheory.MAP]
QED

Theorem registered_case10173_fs_angle_four_sum_argument_results:
  registered_case10173_fs_interval_sum_object [r0;r1;r2;r3] =
    SOME result /\
  12 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) = (M_success (from_cv r0),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs = (M_success (from_cv r1),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs = (M_success (from_cv r2),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument3 refs = (M_success (from_cv r3),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_hist_four»
          [argument0;argument1;argument2;argument3]]) refs =
    (M_success (from_cv result),refs)
Proof
  rpt strip_tac
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval clock registered_case10173_historical_chunk16_ceqs
          (App «candle_cv_fs_angle_interval_sum»
            [from_cv (registered_case10173_cv_list [r0;r1;r2;r3])]) refs`
  >> conj_tac
  >- (irule
        compute_registeredCase10173CanonicalEvalTheory.compute_eval_app1_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> irule EQ_TRANS
      >> qexists_tac
           `compute_eval clock registered_case10173_historical_chunk16_ceqs
              (App «candle_cv_fs_hist_four»
                [from_cv r0;from_cv r1;from_cv r2;from_cv r3]) refs`
      >> conj_tac
      >- (irule
            compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_app4_argument_results
          >> simp [])
      >> irule
           compute_registeredCase10173HistoricalTupleEvalTheory.registered_case10173_fs_hist_four_eval
      >> intLib.ARITH_TAC)
  >> irule
       compute_registeredCase10173HistoricalListEvalTheory.registered_case10173_fs_angle_interval_sum_object_list_eval
  >> simp []
QED

Theorem registered_case10173_fs_angle_four_sum_typed_argument_results:
  bounded_interval64_sum [r0;r1;r2;r3] = SOME result /\
  12 < clock /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument0 (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv r0)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument1 refs =
    (M_success (from_cv (bounded_interval64_object_cv r1)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument2 refs =
    (M_success (from_cv (bounded_interval64_object_cv r2)),refs) /\
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      argument3 refs =
    (M_success (from_cv (bounded_interval64_object_cv r3)),refs) ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_hist_four»
          [argument0;argument1;argument2;argument3]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_four_sum_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv r0`
  >> qexists_tac `bounded_interval64_object_cv r1`
  >> qexists_tac `bounded_interval64_object_cv r2`
  >> qexists_tac `bounded_interval64_object_cv r3`
  >> conj_tac
  >- (irule registered_case10173_interval_sum_object_four_typed_exact
      >> simp [])
  >> simp []
QED

Theorem registered_case10173_fs_hist_final_hessian_diagonal_identity_typed_eval:
  bounded_interval64_add (bounded_interval64_neg first_term) common_last =
      SOME identity /\
  8 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [from_cv
           (bounded_interval64_object_cv (bounded_interval64_neg first_term));
         from_cv (bounded_interval64_object_cv common_last)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv identity)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_interval_add_eval
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact]
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_offdiagonal_identity_typed_eval:
  rowindex < 6 /\ colindex < 6 /\
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  bounded_interval64_mul_decimal
      (EL rowindex delta_x4_gradient) (EL colindex b_gradient) =
    SOME second_term /\
  bounded_interval64_mul_decimal
      (EL colindex delta_x4_gradient) (EL rowindex b_gradient) =
    SOME third_term /\
  bounded_interval64_sum
      [bounded_interval64_neg first_term;
       bounded_interval64_neg second_term;third_term;common_last] =
    SOME identity /\
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_angle_interval_sum»
        [App «candle_cv_fs_hist_four»
          [from_cv
             (bounded_interval64_object_cv
               (bounded_interval64_neg first_term));
           App «candle_cv_fs_interval_neg»
             [App «candle_cv_fs_angle_interval_mul»
               [App «candle_cv_fs_interval_lookup»
                  [from_cv (Num rowindex);
                   from_cv
                     (bounded_interval64_object_cv_list delta_x4_gradient)];
                App «candle_cv_fs_interval_lookup»
                  [from_cv (Num colindex);
                   from_cv (bounded_interval64_object_cv_list b_gradient)]]];
           App «candle_cv_fs_angle_interval_mul»
             [App «candle_cv_fs_interval_lookup»
                [from_cv (Num colindex);
                 from_cv
                   (bounded_interval64_object_cv_list delta_x4_gradient)];
              App «candle_cv_fs_interval_lookup»
                [from_cv (Num rowindex);
                 from_cv (bounded_interval64_object_cv_list b_gradient)]];
           from_cv (bounded_interval64_object_cv common_last)]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv identity)),refs)
Proof
  rpt strip_tac
  >> irule registered_case10173_fs_angle_four_sum_typed_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_neg first_term`
  >> qexists_tac `bounded_interval64_neg second_term`
  >> qexists_tac `third_term`
  >> qexists_tac `common_last`
  >> simp [compute_execProofTheory.compute_eval_from_cv]
  >> conj_tac
  >- (irule registered_case10173_fs_interval_neg_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_object_cv second_term`
      >> simp
           [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_mul_list_lookups_typed_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_mul_list_lookups_typed_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_finish_typed_eval:
  rowindex < 6 /\ colindex < 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  bounded_interval64_mul_decimal reciprocal_u identity =
    SOME scaled_identity /\
  bounded_interval64_mul_decimal (EL rowindex result_gradient)
      (EL colindex logarithmic_u_gradient) = SOME logarithmic_term /\
  bounded_interval64_add scaled_identity
      (bounded_interval64_neg logarithmic_term) = SOME result /\
  30 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_interval_add»
        [App «candle_cv_fs_angle_interval_mul»
           [from_cv (bounded_interval64_object_cv reciprocal_u);
            from_cv (bounded_interval64_object_cv identity)];
         App «candle_cv_fs_interval_neg»
           [App «candle_cv_fs_angle_interval_mul»
             [App «candle_cv_fs_interval_lookup»
                [from_cv (Num rowindex);
                 from_cv
                   (bounded_interval64_object_cv_list result_gradient)];
              App «candle_cv_fs_interval_lookup»
                [from_cv (Num colindex);
                 from_cv
                   (bounded_interval64_object_cv_list
                     logarithmic_u_gradient)]]]]) refs =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> irule
       compute_registeredCase10173HistoricalAtanEvalTheory.registered_case10173_fs_interval_add_argument_results
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv scaled_identity`
  >> qexists_tac
       `bounded_interval64_object_cv (bounded_interval64_neg logarithmic_term)`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_add_object_cv_exact]
  >> conj_tac
  >- (irule
        compute_registeredCase10173HistoricalIntervalEvalTheory.registered_case10173_fs_angle_interval_mul_eval
      >> simp
           [compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact]
      >> intLib.ARITH_TAC)
  >> irule registered_case10173_fs_interval_neg_argument_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `bounded_interval64_object_cv logarithmic_term`
  >> simp
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_mul_list_lookups_typed_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_hist_final_hessian_entry_instantiated_def:
  registered_case10173_fs_hist_final_hessian_entry_instantiated rowindex
      colindex b delta_x4_value delta_x4_gradient delta_x4_hessian
      b_gradient b_hessian reciprocal_u result_gradient log_u_gradient =
    Let «common_first»
      (App «candle_cv_fs_interval_neg»
        [App «candle_cv_fs_angle_interval_mul»
          [b;
           App «candle_cv_fs_angle_matrix_lookup»
             [rowindex;colindex;delta_x4_hessian]]])
      (Let «common_last»
        (App «candle_cv_fs_angle_interval_mul»
          [delta_x4_value;
           App «candle_cv_fs_angle_matrix_lookup»
             [rowindex;colindex;b_hessian]])
        (Let «identity»
          (If (Binop Eq rowindex colindex)
            (App «candle_cv_fs_interval_add»
              [Var «common_first»;Var «common_last»])
            (App «candle_cv_fs_angle_interval_sum»
              [App «candle_cv_fs_hist_four»
                [Var «common_first»;
                 App «candle_cv_fs_interval_neg»
                   [App «candle_cv_fs_angle_interval_mul»
                     [App «candle_cv_fs_interval_lookup»
                        [rowindex;delta_x4_gradient];
                      App «candle_cv_fs_interval_lookup»
                        [colindex;b_gradient]]];
                 App «candle_cv_fs_angle_interval_mul»
                   [App «candle_cv_fs_interval_lookup»
                      [colindex;delta_x4_gradient];
                    App «candle_cv_fs_interval_lookup»
                      [rowindex;b_gradient]];
                 Var «common_last»]]))
          (App «candle_cv_fs_interval_add»
            [App «candle_cv_fs_angle_interval_mul»
               [reciprocal_u;Var «identity»];
             App «candle_cv_fs_interval_neg»
               [App «candle_cv_fs_angle_interval_mul»
                 [App «candle_cv_fs_interval_lookup»
                    [rowindex;result_gradient];
                  App «candle_cv_fs_interval_lookup»
                    [colindex;log_u_gradient]]]])))
End

Theorem registered_case10173_fs_hist_final_hessian_entry_body_subst:
  subst
    [(«rowindex»,rowindex);(«colindex»,colindex);(«b»,b);
     («delta_x4_value»,delta_x4_value);
     («delta_x4_gradient»,delta_x4_gradient);
     («delta_x4_hessian»,delta_x4_hessian);
     («b_gradient»,b_gradient);(«b_hessian»,b_hessian);
     («reciprocal_u»,reciprocal_u);(«result_gradient»,result_gradient);
     («log_u_gradient»,log_u_gradient)]
    registered_case10173_fs_hist_final_hessian_entry_body =
  registered_case10173_fs_hist_final_hessian_entry_instantiated rowindex
    colindex b delta_x4_value delta_x4_gradient delta_x4_hessian
    b_gradient b_hessian reciprocal_u result_gradient log_u_gradient
Proof
  rw
    [registered_case10173_fs_hist_final_hessian_entry_body_def,
     registered_case10173_fs_hist_final_hessian_entry_instantiated_def]
  >> EVAL_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_entry_rows_typed_eval:
  rowindex < 6 /\ colindex < 6 /\
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  LENGTH delta_x4_rows = 6 /\
  EVERY (\row. LENGTH row = 6) delta_x4_rows /\
  LENGTH b_rows = 6 /\
  EVERY (\row. LENGTH row = 6) b_rows /\
  registered_case10173_final_hessian_entry_rows_decimal delta_x4 b
    reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
    result_gradient logarithmic_u_gradient rowindex colindex = SOME result /\
  120 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian_entry»
        [from_cv (Num rowindex);from_cv (Num colindex);
         from_cv (bounded_interval64_object_cv b);
         from_cv (bounded_interval64_object_cv delta_x4);
         from_cv (bounded_interval64_object_cv_list delta_x4_gradient);
         from_cv (bounded_interval64_object_cv_matrix delta_x4_rows);
         from_cv (bounded_interval64_object_cv_list b_gradient);
         from_cv (bounded_interval64_object_cv_matrix b_rows);
         from_cv (bounded_interval64_object_cv reciprocal_u);
         from_cv (bounded_interval64_object_cv_list result_gradient);
         from_cv (bounded_interval64_object_cv_list logarithmic_u_gradient)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> rw [registered_case10173_fs_hist_final_hessian_entry_unfold]
  >> rw
       [registered_case10173_fs_hist_final_hessian_entry_body_subst,
        registered_case10173_fs_hist_final_hessian_entry_instantiated_def]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> Cases_on `rowindex = colindex`
  >- (drule_all_then strip_assume_tac
        registered_case10173_final_hessian_entry_diagonal_trace
      >> qexists_tac
           `from_cv
             (bounded_interval64_object_cv
               (bounded_interval64_neg first_term))`
      >> conj_tac
      >- (irule registered_case10173_fs_interval_neg_argument_result
          >> conj_tac >- intLib.ARITH_TAC
          >> qexists_tac `bounded_interval64_object_cv first_term`
          >> simp
               [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
          >> irule
               (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
                 registered_case10173_fs_hist_mul_matrix_lookup_typed_eval)
          >> fs [EVERY_EL]
          >> metis_tac [])
      >> simp
           [compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
      >> irule
           compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `from_cv (bounded_interval64_object_cv common_last)`
      >> conj_tac
      >- (irule
            (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
              registered_case10173_fs_hist_mul_matrix_lookup_typed_eval)
          >> fs [EVERY_EL]
          >> metis_tac [])
      >> simp
           [compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
      >> irule
           compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `from_cv (bounded_interval64_object_cv identity)`
      >> conj_tac
      >- (simp
            [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
             compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
          >> irule
               registered_case10173_fs_hist_final_hessian_diagonal_identity_typed_eval
          >> simp []
          >> metis_tac [])
      >> simp
           [compute_evalTheory.subst_def,
            compute_execProofTheory.subst_from_cv]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_final_hessian_finish_typed_eval)
      >> simp []
      >> metis_tac [])
  >> drule_all_then strip_assume_tac
       registered_case10173_final_hessian_entry_offdiagonal_trace
  >> qexists_tac
       `from_cv
         (bounded_interval64_object_cv (bounded_interval64_neg first_term))`
  >> conj_tac
  >- (irule registered_case10173_fs_interval_neg_argument_result
      >> conj_tac >- intLib.ARITH_TAC
      >> qexists_tac `bounded_interval64_object_cv first_term`
      >> simp
           [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_mul_matrix_lookup_typed_eval)
      >> fs [EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv common_last)`
  >> conj_tac
  >- (irule
        (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
          registered_case10173_fs_hist_mul_matrix_lookup_typed_eval)
      >> fs [EVERY_EL]
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_let_success_result
  >> conj_tac >- intLib.ARITH_TAC
  >> qexists_tac `from_cv (bounded_interval64_object_cv identity)`
  >> conj_tac
      >- (simp
        [compute_registeredCase10173HistoricalDeltaGradientBoxEvalTheory.registered_case10173_compute_eval_num_eq,
         compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_final_hessian_offdiagonal_identity_typed_eval)
      >> simp []
      >> intLib.ARITH_TAC)
  >> simp
       [compute_evalTheory.subst_def,
        compute_execProofTheory.subst_from_cv]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_final_hessian_finish_typed_eval)
  >> simp []
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_hist_final_hessian_symmetric_entry_body_def:
  registered_case10173_fs_hist_final_hessian_symmetric_entry_body =
    If (Binop Less (Var «colindex») (Var «rowindex»))
      (App «candle_cv_fs_hist_final_hessian_entry»
        [Var «colindex»;Var «rowindex»;Var «b»;Var «delta_x4_value»;
         Var «delta_x4_gradient»;Var «delta_x4_hessian»;
         Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
         Var «result_gradient»;Var «log_u_gradient»])
      (App «candle_cv_fs_hist_final_hessian_entry»
        [Var «rowindex»;Var «colindex»;Var «b»;Var «delta_x4_value»;
         Var «delta_x4_gradient»;Var «delta_x4_hessian»;
         Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
         Var «result_gradient»;Var «log_u_gradient»])
End

Theorem registered_case10173_fs_hist_final_hessian_symmetric_entry_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_final_hessian_symmetric_entry» =
    SOME
      ([«rowindex»;«colindex»;«b»;«delta_x4_value»;
        «delta_x4_gradient»;«delta_x4_hessian»;«b_gradient»;«b_hessian»;
        «reciprocal_u»;«result_gradient»;«log_u_gradient»],
       registered_case10173_fs_hist_final_hessian_symmetric_entry_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_symmetric_entry_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian_symmetric_entry»
        [from_cv rowindex;from_cv colindex;from_cv b;from_cv delta_x4_value;
         from_cv delta_x4_gradient;from_cv delta_x4_hessian;
         from_cv b_gradient;from_cv b_hessian;from_cv reciprocal_u;
         from_cv result_gradient;from_cv log_u_gradient]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);(«colindex»,from_cv colindex);
         («b»,from_cv b);(«delta_x4_value»,from_cv delta_x4_value);
         («delta_x4_gradient»,from_cv delta_x4_gradient);
         («delta_x4_hessian»,from_cv delta_x4_hessian);
         («b_gradient»,from_cv b_gradient);(«b_hessian»,from_cv b_hessian);
         («reciprocal_u»,from_cv reciprocal_u);
         («result_gradient»,from_cv result_gradient);
         («log_u_gradient»,from_cv log_u_gradient)]
        registered_case10173_fs_hist_final_hessian_symmetric_entry_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_final_hessian_symmetric_entry_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_final_hessian_symmetric_entry_rows_typed_eval:
  rowindex < 6 /\ colindex < 6 /\
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  LENGTH delta_x4_rows = 6 /\
  EVERY (\row. LENGTH row = 6) delta_x4_rows /\
  LENGTH b_rows = 6 /\
  EVERY (\row. LENGTH row = 6) b_rows /\
  registered_case10173_final_hessian_symmetric_entry_rows_decimal delta_x4 b
    reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
    result_gradient logarithmic_u_gradient rowindex colindex = SOME result /\
  122 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian_symmetric_entry»
        [from_cv (Num rowindex);from_cv (Num colindex);
         from_cv (bounded_interval64_object_cv b);
         from_cv (bounded_interval64_object_cv delta_x4);
         from_cv (bounded_interval64_object_cv_list delta_x4_gradient);
         from_cv (bounded_interval64_object_cv_matrix delta_x4_rows);
         from_cv (bounded_interval64_object_cv_list b_gradient);
         from_cv (bounded_interval64_object_cv_matrix b_rows);
         from_cv (bounded_interval64_object_cv reciprocal_u);
         from_cv (bounded_interval64_object_cv_list result_gradient);
         from_cv (bounded_interval64_object_cv_list logarithmic_u_gradient)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_final_hessian_symmetric_entry_unfold]
  >> simp
       [registered_case10173_fs_hist_final_hessian_symmetric_entry_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on `colindex < rowindex`
  >- (`compute_eval (clock - 1)
          registered_case10173_historical_chunk16_ceqs
          (Binop Less (Num colindex) (Num rowindex)) refs =
        (M_success (Num 1),refs)` by
       simp
         [compute_evalTheory.compute_eval_def,
          compute_evalTheory.do_binop_def,
          compute_evalTheory.do_reln_def,
          ml_monadBaseTheory.st_ex_bind_def,
          ml_monadBaseTheory.st_ex_return_def]
      >> simp
           [compute_registeredCase10173CheckedJobsEvalTheory.compute_eval_if_success]
      >> irule
           (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
             registered_case10173_fs_hist_final_hessian_entry_rows_typed_eval)
      >> fs
           [registered_case10173_final_hessian_symmetric_entry_rows_decimal_def]
      >> intLib.ARITH_TAC)
  >> `compute_eval (clock - 1)
        registered_case10173_historical_chunk16_ceqs
        (Binop Less (Num colindex) (Num rowindex)) refs =
      (M_success (Num 0),refs)` by
     simp
       [compute_evalTheory.compute_eval_def,
        compute_evalTheory.do_binop_def,
        compute_evalTheory.do_reln_def,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
  >> simp
       [compute_registeredCase10173HistStepEvalTheory.registered_case10173_compute_eval_if_zero]
  >> irule
       (SIMP_RULE std_ss [compute_execTheory.from_cv_def]
         registered_case10173_fs_hist_final_hessian_entry_rows_typed_eval)
  >> fs [registered_case10173_final_hessian_symmetric_entry_rows_decimal_def]
  >> intLib.ARITH_TAC
QED

Definition registered_case10173_fs_hist_final_hessian_row_body_def:
  registered_case10173_fs_hist_final_hessian_row_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_hist_final_hessian_symmetric_entry»
         [Var «rowindex»;Num 0;Var «b»;Var «delta_x4_value»;
          Var «delta_x4_gradient»;Var «delta_x4_hessian»;
          Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
          Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_symmetric_entry»
         [Var «rowindex»;Num 1;Var «b»;Var «delta_x4_value»;
          Var «delta_x4_gradient»;Var «delta_x4_hessian»;
          Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
          Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_symmetric_entry»
         [Var «rowindex»;Num 2;Var «b»;Var «delta_x4_value»;
          Var «delta_x4_gradient»;Var «delta_x4_hessian»;
          Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
          Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_symmetric_entry»
         [Var «rowindex»;Num 3;Var «b»;Var «delta_x4_value»;
          Var «delta_x4_gradient»;Var «delta_x4_hessian»;
          Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
          Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_symmetric_entry»
         [Var «rowindex»;Num 4;Var «b»;Var «delta_x4_value»;
          Var «delta_x4_gradient»;Var «delta_x4_hessian»;
          Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
          Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_symmetric_entry»
         [Var «rowindex»;Num 5;Var «b»;Var «delta_x4_value»;
          Var «delta_x4_gradient»;Var «delta_x4_hessian»;
          Var «b_gradient»;Var «b_hessian»;Var «reciprocal_u»;
          Var «result_gradient»;Var «log_u_gradient»]]
End

Theorem registered_case10173_fs_hist_final_hessian_row_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_final_hessian_row» =
    SOME
      ([«rowindex»;«b»;«delta_x4_value»;«delta_x4_gradient»;
        «delta_x4_hessian»;«b_gradient»;«b_hessian»;«reciprocal_u»;
        «result_gradient»;«log_u_gradient»],
       registered_case10173_fs_hist_final_hessian_row_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_row_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian_row»
        [from_cv rowindex;from_cv b;from_cv delta_x4_value;
         from_cv delta_x4_gradient;from_cv delta_x4_hessian;
         from_cv b_gradient;from_cv b_hessian;from_cv reciprocal_u;
         from_cv result_gradient;from_cv log_u_gradient]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«rowindex»,from_cv rowindex);(«b»,from_cv b);
         («delta_x4_value»,from_cv delta_x4_value);
         («delta_x4_gradient»,from_cv delta_x4_gradient);
         («delta_x4_hessian»,from_cv delta_x4_hessian);
         («b_gradient»,from_cv b_gradient);(«b_hessian»,from_cv b_hessian);
         («reciprocal_u»,from_cv reciprocal_u);
         («result_gradient»,from_cv result_gradient);
         («log_u_gradient»,from_cv log_u_gradient)]
        registered_case10173_fs_hist_final_hessian_row_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_final_hessian_row_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_final_hessian_row_rows_typed_eval:
  rowindex < 6 /\
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  LENGTH delta_x4_rows = 6 /\
  EVERY (\row. LENGTH row = 6) delta_x4_rows /\
  LENGTH b_rows = 6 /\
  EVERY (\row. LENGTH row = 6) b_rows /\
  registered_case10173_final_hessian_row_rows_decimal delta_x4 b
    reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
    result_gradient logarithmic_u_gradient rowindex = SOME result /\
  124 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian_row»
        [from_cv (Num rowindex);from_cv (bounded_interval64_object_cv b);
         from_cv (bounded_interval64_object_cv delta_x4);
         from_cv (bounded_interval64_object_cv_list delta_x4_gradient);
         from_cv (bounded_interval64_object_cv_matrix delta_x4_rows);
         from_cv (bounded_interval64_object_cv_list b_gradient);
         from_cv (bounded_interval64_object_cv_matrix b_rows);
         from_cv (bounded_interval64_object_cv reciprocal_u);
         from_cv (bounded_interval64_object_cv_list result_gradient);
         from_cv (bounded_interval64_object_cv_list logarithmic_u_gradient)])
      (refs:hol_refs) =
    (M_success (from_cv (bounded_interval64_object_cv_list result)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_final_hessian_row_unfold]
  >> simp
       [registered_case10173_fs_hist_final_hessian_row_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 0`
  >> gvs [registered_case10173_final_hessian_row_rows_decimal_def]
  >> Cases_on
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 1`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 2`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 3`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 4`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 5`
  >> gvs []
  >> rename1
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 0 = SOME r0`
  >> rename1
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 1 = SOME r1`
  >> rename1
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 2 = SOME r2`
  >> rename1
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 3 = SOME r3`
  >> rename1
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
          rowindex 4 = SOME r4`
  >> rename1
       `registered_case10173_final_hessian_symmetric_entry_rows_decimal
          delta_x4 b reciprocal_u delta_x4_gradient delta_x4_rows
          b_gradient b_rows result_gradient logarithmic_u_gradient
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
             registered_case10173_fs_hist_final_hessian_symmetric_entry_rows_typed_eval)
      >> fs []
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

Definition registered_case10173_fs_hist_final_hessian_body_def:
  registered_case10173_fs_hist_final_hessian_body =
    App «candle_cv_fs_angle_six»
      [App «candle_cv_fs_hist_final_hessian_row»
         [Num 0;Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
          Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
          Var «reciprocal_u»;Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_row»
         [Num 1;Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
          Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
          Var «reciprocal_u»;Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_row»
         [Num 2;Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
          Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
          Var «reciprocal_u»;Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_row»
         [Num 3;Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
          Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
          Var «reciprocal_u»;Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_row»
         [Num 4;Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
          Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
          Var «reciprocal_u»;Var «result_gradient»;Var «log_u_gradient»];
       App «candle_cv_fs_hist_final_hessian_row»
         [Num 5;Var «b»;Var «delta_x4_value»;Var «delta_x4_gradient»;
          Var «delta_x4_hessian»;Var «b_gradient»;Var «b_hessian»;
          Var «reciprocal_u»;Var «result_gradient»;Var «log_u_gradient»]]
End

Theorem registered_case10173_fs_hist_final_hessian_lookup:
  ALOOKUP registered_case10173_historical_chunk16_ceqs
      «candle_cv_fs_hist_final_hessian» =
    SOME
      ([«b»;«delta_x4_value»;«delta_x4_gradient»;«delta_x4_hessian»;
        «b_gradient»;«b_hessian»;«reciprocal_u»;«result_gradient»;
        «log_u_gradient»],registered_case10173_fs_hist_final_hessian_body)
Proof
  EVAL_TAC
QED

Theorem registered_case10173_fs_hist_final_hessian_unfold:
  0 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian»
        [from_cv b;from_cv delta_x4_value;from_cv delta_x4_gradient;
         from_cv delta_x4_hessian;from_cv b_gradient;from_cv b_hessian;
         from_cv reciprocal_u;from_cv result_gradient;
         from_cv log_u_gradient]) (refs:hol_refs) =
    compute_eval (clock - 1)
      registered_case10173_historical_chunk16_ceqs
      (subst
        [(«b»,from_cv b);(«delta_x4_value»,from_cv delta_x4_value);
         («delta_x4_gradient»,from_cv delta_x4_gradient);
         («delta_x4_hessian»,from_cv delta_x4_hessian);
         («b_gradient»,from_cv b_gradient);(«b_hessian»,from_cv b_hessian);
         («reciprocal_u»,from_cv reciprocal_u);
         («result_gradient»,from_cv result_gradient);
         («log_u_gradient»,from_cv log_u_gradient)]
        registered_case10173_fs_hist_final_hessian_body) refs
Proof
  Cases_on `clock`
  >> simp
       [Once compute_evalTheory.compute_eval_def,
        registered_case10173_fs_hist_final_hessian_lookup,
        compute_evalTheory.compute_eval_def,
        compute_evalTheory.subst_def,
        compute_evalTheory.option_def,
        compute_evalTheory.check_def,
        compute_execProofTheory.compute_eval_from_cv,
        ml_monadBaseTheory.st_ex_bind_def,
        ml_monadBaseTheory.st_ex_ignore_bind_def,
        ml_monadBaseTheory.st_ex_return_def]
QED

Theorem registered_case10173_fs_hist_final_hessian_rows_typed_eval:
  LENGTH delta_x4_gradient = 6 /\
  LENGTH b_gradient = 6 /\
  LENGTH result_gradient = 6 /\
  LENGTH logarithmic_u_gradient = 6 /\
  LENGTH delta_x4_rows = 6 /\
  EVERY (\row. LENGTH row = 6) delta_x4_rows /\
  LENGTH b_rows = 6 /\
  EVERY (\row. LENGTH row = 6) b_rows /\
  registered_case10173_final_hessian_rows_decimal delta_x4 b reciprocal_u
    delta_x4_gradient delta_x4_rows b_gradient b_rows result_gradient
    logarithmic_u_gradient = SOME result_rows /\
  126 < clock ==>
  compute_eval clock registered_case10173_historical_chunk16_ceqs
      (App «candle_cv_fs_hist_final_hessian»
        [from_cv (bounded_interval64_object_cv b);
         from_cv (bounded_interval64_object_cv delta_x4);
         from_cv (bounded_interval64_object_cv_list delta_x4_gradient);
         from_cv (bounded_interval64_object_cv_matrix delta_x4_rows);
         from_cv (bounded_interval64_object_cv_list b_gradient);
         from_cv (bounded_interval64_object_cv_matrix b_rows);
         from_cv (bounded_interval64_object_cv reciprocal_u);
         from_cv (bounded_interval64_object_cv_list result_gradient);
         from_cv (bounded_interval64_object_cv_list logarithmic_u_gradient)])
      (refs:hol_refs) =
    (M_success
      (from_cv (bounded_interval64_object_cv_matrix result_rows)),refs)
Proof
  rpt strip_tac
  >> simp [registered_case10173_fs_hist_final_hessian_unfold]
  >> simp
       [registered_case10173_fs_hist_final_hessian_body_def,
        compute_evalTheory.subst_def]
  >> Cases_on
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 0`
  >> gvs [registered_case10173_final_hessian_rows_decimal_def]
  >> Cases_on
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 1`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 2`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 3`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 4`
  >> gvs []
  >> Cases_on
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 5`
  >> gvs []
  >> rename1
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 0 = SOME r0`
  >> rename1
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 1 = SOME r1`
  >> rename1
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 2 = SOME r2`
  >> rename1
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 3 = SOME r3`
  >> rename1
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 4 = SOME r4`
  >> rename1
       `registered_case10173_final_hessian_row_rows_decimal delta_x4 b
          reciprocal_u delta_x4_gradient delta_x4_rows b_gradient b_rows
          result_gradient logarithmic_u_gradient 5 = SOME r5`
  >> irule EQ_TRANS
  >> qexists_tac
       `compute_eval (clock - 1)
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
             registered_case10173_fs_hist_final_hessian_row_rows_typed_eval)
      >> fs []
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
