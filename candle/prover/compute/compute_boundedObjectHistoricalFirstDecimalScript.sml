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

Definition bounded_object_fs_signed_interval_list_def:
  bounded_object_fs_signed_interval_list [] = SOME (Num 0 : cv) /\
  bounded_object_fs_signed_interval_list ((negative,value)::rest) =
    case (if negative then
            bounded_object_fs_interval_neg
              (bounded_interval64_object_cv value)
          else SOME (bounded_interval64_object_cv value)) of
    | NONE => NONE
    | SOME signed_value =>
      case bounded_object_fs_signed_interval_list rest of
      | NONE => NONE
      | SOME signed_rest => SOME (Pair signed_value signed_rest)
End

Theorem bounded_object_fs_signed_interval_list_exact:
  !entries.
    bounded_object_fs_signed_interval_list entries =
      SOME
        (bounded_interval64_object_cv_list
          (MAP (\(negative,value).
             if negative then bounded_interval64_neg value else value)
           entries))
Proof
  Induct
  >- simp [bounded_object_fs_signed_interval_list_def,
           compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> gen_tac
  >> PairCases_on `h`
  >> Cases_on `h0`
  >> simp [bounded_object_fs_signed_interval_list_def,
           compute_boundedObjectDecimalAddTheory.bounded_object_fs_interval_neg_object_cv_exact,
           compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_interval_sum_signed_def:
  bounded_object_fs_interval_sum_signed entries =
    case bounded_object_fs_signed_interval_list entries of
    | NONE => NONE
    | SOME values => bounded_object_fs_interval_sum values
End

Theorem bounded_object_fs_interval_sum_signed_exact:
  bounded_interval64_sum
      (MAP (\(negative,value).
         if negative then bounded_interval64_neg value else value) entries) =
    SOME result ==>
  bounded_object_fs_interval_sum_signed entries =
    SOME (bounded_interval64_object_cv result)
Proof
  rw [bounded_object_fs_interval_sum_signed_def,
      bounded_object_fs_signed_interval_list_exact]
  >> metis_tac
       [compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_sum_exact]
QED

Definition bounded_object_fs_delta64_pair_products_decimal_def:
  bounded_object_fs_delta64_pair_products_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      bounded_object_fs_interval_list_pairwise_mul_decimal
        (bounded_interval64_object_cv_list
          [x0;x0;x0;x0;x0;x0;
           x1;x1;x1;x1;x1;
           x2;x2;x2;x2;
           x3;x3;x3;
           x4;x4;
           x5])
        (bounded_interval64_object_cv_list
          [x0;x1;x2;x3;x4;x5;
           x1;x2;x3;x4;x5;
           x2;x3;x4;x5;
           x3;x4;x5;
           x4;x5;
           x5])
    | _ => NONE
End

Theorem bounded_object_fs_delta64_pair_products_decimal_exact:
  bounded_delta64_pair_products_decimal environment = SOME result ==>
  bounded_object_fs_delta64_pair_products_decimal environment =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw [compute_boundedHistoricalDihedralFirstDecimalTheory.bounded_delta64_pair_products_decimal_def,
      bounded_object_fs_delta64_pair_products_decimal_def]
  >> every_case_tac
  >> gvs []
  >> metis_tac
       [compute_boundedObjectHistoricalListDecimalTheory.bounded_object_fs_interval_list_pairwise_mul_decimal_exact]
QED

Definition bounded_object_fs_delta64_gradient_component_from_products_def:
  bounded_object_fs_delta64_gradient_component_from_products (coordinate:num)
      products =
    case bounded_delta64_gradient_signed_terms coordinate products of
    | NONE => NONE
    | SOME terms => bounded_object_fs_interval_sum_signed terms
End

val bounded_delta_gradient_component_defs =
  [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_component_from_products_def,
   compute_boundedDeltaTaylorTheory.bounded_delta64_apply_signed_terms_def,
   bounded_object_fs_delta64_gradient_component_from_products_def];

Theorem bounded_object_fs_delta64_gradient_component_from_products_exact:
  bounded_delta64_gradient_component_from_products coordinate products =
    SOME result ==>
  bounded_object_fs_delta64_gradient_component_from_products coordinate
    products = SOME (bounded_interval64_object_cv result)
Proof
  rw bounded_delta_gradient_component_defs
  >> every_case_tac
  >> gvs []
  >> metis_tac [bounded_object_fs_interval_sum_signed_exact]
QED

Definition bounded_object_fs_delta64_gradient_components_def:
  bounded_object_fs_delta64_gradient_components [] products =
    SOME (Num 0 : cv) /\
  bounded_object_fs_delta64_gradient_components
      (coordinate::coordinates) products =
    case bounded_object_fs_delta64_gradient_component_from_products
      coordinate products of
    | NONE => NONE
    | SOME entry =>
      case bounded_object_fs_delta64_gradient_components coordinates products of
      | NONE => NONE
      | SOME rest => SOME (Pair entry rest)
End

Theorem bounded_object_fs_delta64_gradient_components_exact:
  !products result.
    bounded_delta64_gradient_components coordinates products = SOME result ==>
    bounded_object_fs_delta64_gradient_components coordinates products =
      SOME (bounded_interval64_object_cv_list result)
Proof
  Induct_on `coordinates`
  >> rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_components_def,
         bounded_object_fs_delta64_gradient_components_def,
         compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_object_fs_delta64_gradient_component_from_products_exact
  >> res_tac
  >> gvs
       [compute_boundedObjectDecimalDecodeTheory.bounded_interval64_object_cv_list_def]
QED

Definition bounded_object_fs_delta64_gradient_from_products_def:
  bounded_object_fs_delta64_gradient_from_products products =
    bounded_object_fs_delta64_gradient_components [0;1;2;3;4;5] products
End

Theorem bounded_object_fs_delta64_gradient_from_products_exact:
  bounded_delta64_gradient_from_products products = SOME result ==>
  bounded_object_fs_delta64_gradient_from_products products =
    SOME (bounded_interval64_object_cv_list result)
Proof
  rw [compute_boundedDeltaTaylorTheory.bounded_delta64_gradient_from_products_def,
      bounded_object_fs_delta64_gradient_from_products_def]
  >> metis_tac [bounded_object_fs_delta64_gradient_components_exact]
QED

val _ = export_theory ();
