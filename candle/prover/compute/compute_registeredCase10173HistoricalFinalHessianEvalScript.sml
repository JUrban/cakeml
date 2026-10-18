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

val _ = export_theory ();
