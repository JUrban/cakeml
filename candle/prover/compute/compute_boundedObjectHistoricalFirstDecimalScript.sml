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

Definition bounded_object_fs_historical_delta_x4_gradient_def:
  bounded_object_fs_historical_delta_x4_gradient environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_object_fs_interval_neg
        (bounded_interval64_object_cv x0) of
      | NONE => NONE
      | SOME negative_x0 =>
        case bounded_object_fs_interval_neg
          (bounded_interval64_object_cv x1) of
        | NONE => NONE
        | SOME negative_x1 =>
          case bounded_object_fs_interval_neg
            (bounded_interval64_object_cv x2) of
          | NONE => NONE
          | SOME negative_x2 =>
            case bounded_object_fs_interval_neg
              (bounded_interval64_object_cv x3) of
            | NONE => NONE
            | SOME negative_x3 =>
              case bounded_object_fs_interval_neg
                (bounded_interval64_object_cv x4) of
              | NONE => NONE
              | SOME negative_x4 =>
                case bounded_object_fs_interval_neg
                  (bounded_interval64_object_cv x5) of
                | NONE => NONE
                | SOME negative_x5 =>
                  case bounded_object_fs_interval_sum
                    (Pair negative_x0
                      (Pair negative_x0
                        (Pair (bounded_interval64_object_cv x1)
                          (Pair (bounded_interval64_object_cv x2)
                            (Pair negative_x3
                              (Pair negative_x3
                                (Pair (bounded_interval64_object_cv x4)
                                  (Pair (bounded_interval64_object_cv x5)
                                    (Num 0))))))))) of
                  | NONE => NONE
                  | SOME g0 =>
                    case bounded_object_fs_interval_sum
                      (Pair (bounded_interval64_object_cv x0)
                        (Pair negative_x2
                          (Pair (bounded_interval64_object_cv x4)
                            (Num 0)))) of
                    | NONE => NONE
                    | SOME g1 =>
                      case bounded_object_fs_interval_sum
                        (Pair (bounded_interval64_object_cv x0)
                          (Pair negative_x1
                            (Pair (bounded_interval64_object_cv x5)
                              (Num 0)))) of
                      | NONE => NONE
                      | SOME g2 =>
                        case bounded_object_fs_interval_scale2 negative_x0 of
                        | NONE => NONE
                        | SOME g3 =>
                          case bounded_object_fs_interval_sum
                            (Pair (bounded_interval64_object_cv x0)
                              (Pair (bounded_interval64_object_cv x1)
                                (Pair negative_x5 (Num 0)))) of
                          | NONE => NONE
                          | SOME g4 =>
                            case bounded_object_fs_interval_sum
                              (Pair (bounded_interval64_object_cv x0)
                                (Pair (bounded_interval64_object_cv x2)
                                  (Pair negative_x4 (Num 0)))) of
                            | NONE => NONE
                            | SOME g5 =>
                              SOME
                                (Pair g0
                                  (Pair g1
                                    (Pair g2
                                      (Pair g3
                                        (Pair g4
                                          (Pair g5 (Num 0)))))))
    | _ => NONE
End

Theorem bounded_object_fs_historical_delta_x4_gradient_exact:
  bounded_historical_delta_x4_gradient environment = SOME result ==>
  bounded_object_fs_historical_delta_x4_gradient environment =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_delta_x4_gradient_def,
      bounded_object_fs_historical_delta_x4_gradient_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact
  >> imp_res_tac
       compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_scale2_exact
  >> gvs
       [compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
        compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

val _ = export_theory ();
