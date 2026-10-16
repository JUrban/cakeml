(*****************************************************************************
 * Exact object traces for the historical decimal center calculation.
 *****************************************************************************)
Theory compute_boundedObjectHistoricalFirstDecimal
Ancestors
  compute_boundedObjectHistoricalListDecimal
Libs
  bossLib preamble

Definition bounded_object_fs_historical_delta_x4_value_decimal_def:
  bounded_object_fs_historical_delta_x4_value_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_object_fs_interval_neg
        (bounded_interval64_object_cv x0) of
      | NONE => NONE
      | SOME negative_x0 =>
        case bounded_object_fs_interval_neg
          (bounded_interval64_object_cv x3) of
        | NONE => NONE
        | SOME negative_x3 =>
          case bounded_object_fs_interval_sum
            (Pair negative_x0
              (Pair (bounded_interval64_object_cv x1)
                (Pair (bounded_interval64_object_cv x2)
                  (Pair negative_x3
                    (Pair (bounded_interval64_object_cv x4)
                      (Pair (bounded_interval64_object_cv x5)
                        (Num 0))))))) of
          | NONE => NONE
          | SOME linear =>
            case bounded_object_fs_interval_mul_decimal
              (bounded_interval64_object_cv x1)
              (bounded_interval64_object_cv x2) of
            | NONE => NONE
            | SOME p12 =>
              case bounded_object_fs_interval_mul_decimal
                (bounded_interval64_object_cv x0)
                (bounded_interval64_object_cv x3) of
              | NONE => NONE
              | SOME p03 =>
                case bounded_object_fs_interval_mul_decimal
                  (bounded_interval64_object_cv x1)
                  (bounded_interval64_object_cv x4) of
                | NONE => NONE
                | SOME p14 =>
                  case bounded_object_fs_interval_mul_decimal
                    (bounded_interval64_object_cv x2)
                    (bounded_interval64_object_cv x5) of
                  | NONE => NONE
                  | SOME p25 =>
                    case bounded_object_fs_interval_mul_decimal
                      (bounded_interval64_object_cv x4)
                      (bounded_interval64_object_cv x5) of
                    | NONE => NONE
                    | SOME p45 =>
                      case bounded_object_fs_interval_mul_decimal
                        (bounded_interval64_object_cv x0) linear of
                      | NONE => NONE
                      | SOME p0l =>
                        case bounded_object_fs_interval_neg p12 of
                        | NONE => NONE
                        | SOME negative_p12 =>
                          case bounded_object_fs_interval_neg p03 of
                          | NONE => NONE
                          | SOME negative_p03 =>
                            case bounded_object_fs_interval_neg p45 of
                            | NONE => NONE
                            | SOME negative_p45 =>
                              bounded_object_fs_interval_sum
                                (Pair negative_p12
                                  (Pair negative_p03
                                    (Pair p14
                                      (Pair p25
                                        (Pair negative_p45
                                          (Pair p0l (Num 0)))))))
    | _ => NONE
End

Theorem bounded_object_fs_historical_delta_x4_value_decimal_exact:
  bounded_historical_delta_x4_value_decimal environment = SOME result ==>
  bounded_object_fs_historical_delta_x4_value_decimal environment =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_historical_delta_x4_value_decimal_def,
      bounded_object_fs_historical_delta_x4_value_decimal_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact
  >> imp_res_tac
       compute_boundedObjectDecimalIntervalTheory.bounded_object_fs_interval_mul_decimal_exact
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

val _ = export_theory ();
