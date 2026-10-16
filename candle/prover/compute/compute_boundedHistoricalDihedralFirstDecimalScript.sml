(*****************************************************************************
 * Checked historical Flyspeck dihedral center jet at decimal scale 10^12.
 *
 * Monotone endpoint selection, additions, and list indexing are reused from
 * the historical implementation.  Every operation that rounds a product or
 * authenticates a reciprocal/root is routed through the decimal engine.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralFirstDecimal
Ancestors
  compute_boundedHistoricalDihedralFirst
  compute_boundedHistoricalDeltaDecimal compute_boundedAtanDecimal
  compute_boundedTaylorProductDecimal compute_boundedObjectCertificateDecimal
Libs
  bossLib preamble

Definition bounded_interval64_list_pairwise_mul_decimal_def:
  bounded_interval64_list_pairwise_mul_decimal [] [] = SOME [] /\
  bounded_interval64_list_pairwise_mul_decimal (left::left_rest)
      (right::right_rest) =
    (case bounded_interval64_mul_decimal left right of
     | NONE => NONE
     | SOME value =>
       case bounded_interval64_list_pairwise_mul_decimal
         left_rest right_rest of
       | NONE => NONE
       | SOME rest => SOME (value::rest)) /\
  bounded_interval64_list_pairwise_mul_decimal _ _ = NONE
End

Definition bounded_delta64_pair_products_decimal_def:
  bounded_delta64_pair_products_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      bounded_interval64_list_pairwise_mul_decimal
        [x0;x0;x0;x0;x0;x0;
         x1;x1;x1;x1;x1;
         x2;x2;x2;x2;
         x3;x3;x3;
         x4;x4;
         x5]
        [x0;x1;x2;x3;x4;x5;
         x1;x2;x3;x4;x5;
         x2;x3;x4;x5;
         x3;x4;x5;
         x4;x5;
         x5]
    | _ => NONE
End

Definition bounded_historical_u_block_decimal_def:
  bounded_historical_u_block_decimal n0 n1 n2 p0 p1 p2 =
    bounded_interval64_fused_products_decimal
      [(bounded_interval64_neg n0,n0);
       (bounded_interval64_neg n1,n1);
       (bounded_interval64_neg n2,n2);
       (p0,p1);(p0,p1);
       (p1,p2);(p1,p2);
       (p2,p0);(p2,p0)]
End

Definition bounded_historical_u_three_decimal_def:
  bounded_historical_u_three_decimal x0 x1 x2 =
    case bounded_interval64_sum [bounded_interval64_neg x0;x1;x2] of
    | NONE => NONE
    | SOME g0_half =>
      case bounded_historical_scale2 g0_half of
      | NONE => NONE
      | SOME g0 =>
        case bounded_interval64_sum [x0;bounded_interval64_neg x1;x2] of
        | NONE => NONE
        | SOME g1_half =>
          case bounded_historical_scale2 g1_half of
          | NONE => NONE
          | SOME g1 =>
            case bounded_interval64_sum
              [x0;x1;bounded_interval64_neg x2] of
            | NONE => NONE
            | SOME g2_half =>
              case bounded_historical_scale2 g2_half of
              | NONE => NONE
              | SOME g2 =>
                case bounded_historical_u_block_decimal
                  (bounded_historical_u_lower_negative x0 g0)
                  (bounded_historical_u_lower_negative x1 g1)
                  (bounded_historical_u_lower_negative x2 g2)
                  (bounded_historical_u_lower_positive x0 g0)
                  (bounded_historical_u_lower_positive x1 g1)
                  (bounded_historical_u_lower_positive x2 g2) of
                | NONE => NONE
                | SOME lower_value =>
                  case bounded_historical_u_block_decimal
                    (bounded_historical_u_upper_negative x0 g0)
                    (bounded_historical_u_upper_negative x1 g1)
                    (bounded_historical_u_upper_negative x2 g2)
                    (bounded_historical_u_upper_positive x0 g0)
                    (bounded_historical_u_upper_positive x1 g1)
                    (bounded_historical_u_upper_positive x2 g2) of
                  | NONE => NONE
                  | SOME upper_value =>
                      SOME
                        ((BoundedInterval64
                           (bounded_interval64_lower lower_value)
                           (bounded_interval64_upper upper_value)),
                         [g0;g1;g2])
End

Definition bounded_historical_u126_decimal_def:
  bounded_historical_u126_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_historical_u_three_decimal x0 x1 x5 of
      | NONE => NONE
      | SOME (value,g0::g1::g2::[]) =>
          SOME (value,
            [g0;g1;bounded_interval64_zero;bounded_interval64_zero;
             bounded_interval64_zero;g2])
      | SOME _ => NONE)
    | _ => NONE
End

Definition bounded_historical_u135_decimal_def:
  bounded_historical_u135_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_historical_u_three_decimal x0 x2 x4 of
      | NONE => NONE
      | SOME (value,g0::g1::g2::[]) =>
          SOME (value,
            [g0;bounded_interval64_zero;g1;bounded_interval64_zero;
             g2;bounded_interval64_zero])
      | SOME _ => NONE)
    | _ => NONE
End

Definition bounded_historical_delta_x4_value_decimal_def:
  bounded_historical_delta_x4_value_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_interval64_sum
        [bounded_interval64_neg x0;x1;x2;
         bounded_interval64_neg x3;x4;x5] of
      | NONE => NONE
      | SOME linear =>
        case bounded_interval64_mul_decimal x1 x2 of
        | NONE => NONE
        | SOME p12 =>
          case bounded_interval64_mul_decimal x0 x3 of
          | NONE => NONE
          | SOME p03 =>
            case bounded_interval64_mul_decimal x1 x4 of
            | NONE => NONE
            | SOME p14 =>
              case bounded_interval64_mul_decimal x2 x5 of
              | NONE => NONE
              | SOME p25 =>
                case bounded_interval64_mul_decimal x4 x5 of
                | NONE => NONE
                | SOME p45 =>
                  case bounded_interval64_mul_decimal x0 linear of
                  | NONE => NONE
                  | SOME p0l =>
                      bounded_interval64_sum
                        [bounded_interval64_neg p12;
                         bounded_interval64_neg p03;p14;p25;
                         bounded_interval64_neg p45;p0l])
    | _ => NONE
End

Definition bounded_historical_c_vector_decimal_def:
  bounded_historical_c_vector_decimal delta_x4 b [] [] = SOME [] /\
  bounded_historical_c_vector_decimal delta_x4 b
      (delta_gradient::delta_rest) (b_gradient::b_rest) =
    (case bounded_interval64_mul_decimal delta_gradient b of
     | NONE => NONE
     | SOME first_product =>
       case bounded_interval64_mul_decimal delta_x4 b_gradient of
       | NONE => NONE
       | SOME second_product =>
         case bounded_interval64_add
           (bounded_interval64_neg first_product) second_product of
         | NONE => NONE
         | SOME value =>
           case bounded_historical_c_vector_decimal
             delta_x4 b delta_rest b_rest of
           | NONE => NONE
           | SOME rest => SOME (value::rest)) /\
  bounded_historical_c_vector_decimal delta_x4 b _ _ = NONE
End

Definition bounded_historical_dihedral_first64_decimal_def:
  bounded_historical_dihedral_first64_decimal environment root_delta
      root_four_x0 reciprocal_certificates =
    case reciprocal_certificates of
    | root_derivative::root_four_reciprocal::u_reciprocal::
        special_root_reciprocal::b_reciprocal::[] =>
      (case bounded_historical_delta64_value_decimal environment of
      | NONE => NONE
      | SOME delta_interval =>
        if ¬bounded_interval64_sqrt_certificate_decimal delta_interval root_delta
        then NONE
        else
          case bounded_interval64_nth environment 0 of
          | NONE => NONE
          | SOME x0 =>
            case bounded_interval64_scale4 x0 of
            | NONE => NONE
            | SOME four_x0 =>
              if ¬bounded_interval64_sqrt_certificate_decimal
                  four_x0 root_four_x0 then NONE
              else
                case bounded_historical_scale2 root_delta of
                | NONE => NONE
                | SOME twice_root_delta =>
                  if ¬bounded_interval64_positive_inv_certificate_decimal
                      twice_root_delta root_derivative then NONE
                  else if ¬bounded_interval64_positive_inv_certificate_decimal
                      twice_root_delta special_root_reciprocal then NONE
                  else if ¬bounded_interval64_positive_inv_certificate_decimal
                      root_four_x0 root_four_reciprocal then NONE
                  else
                    case bounded_delta64_pair_products_decimal environment of
                    | NONE => NONE
                    | SOME delta_products =>
                      case bounded_delta64_gradient_from_products
                        delta_products of
                      | NONE => NONE
                      | SOME delta_gradient =>
                        case bounded_interval64_list_scale_decimal
                          root_derivative delta_gradient of
                        | NONE => NONE
                        | SOME root_gradient =>
                          case bounded_historical_delta_x4_value_decimal
                            environment of
                          | NONE => NONE
                          | SOME delta_x4 =>
                            case bounded_historical_delta_x4_gradient
                              environment of
                            | NONE => NONE
                            | SOME delta_x4_gradient =>
                              case bounded_historical_u126_decimal
                                environment of
                              | NONE => NONE
                              | SOME (u126,u126_gradient) =>
                                case bounded_historical_u135_decimal
                                  environment of
                                | NONE => NONE
                                | SOME (u135,u135_gradient) =>
                                  case bounded_interval64_mul_decimal
                                    root_delta root_four_x0 of
                                  | NONE => NONE
                                  | SOME b =>
                                    if ¬bounded_interval64_positive_inv_certificate_decimal
                                        b b_reciprocal then NONE
                                    else
                                      case bounded_interval64_mul_decimal
                                        u126 u135 of
                                      | NONE => NONE
                                      | SOME u_product =>
                                        if ¬bounded_interval64_positive_inv_certificate_decimal
                                            u_product u_reciprocal then NONE
                                        else
                                          case bounded_historical_scale2
                                            bounded_atan_one_decimal of
                                          | NONE => NONE
                                          | SOME two =>
                                            case bounded_interval64_mul_decimal
                                              two root_four_reciprocal of
                                            | NONE => NONE
                                            | SOME two_over_root_four =>
                                              case bounded_interval64_list_scale_decimal
                                                root_four_x0 root_gradient of
                                              | NONE => NONE
                                              | SOME b_gradient_base =>
                                                case bounded_interval64_mul_decimal
                                                  root_delta
                                                  two_over_root_four of
                                                | NONE => NONE
                                                | SOME b_correction =>
                                                  case
                                                    bounded_interval64_list_add_at
                                                      b_correction 0
                                                      b_gradient_base of
                                                  | NONE => NONE
                                                  | SOME b_gradient =>
                                                    case
                                                      bounded_historical_c_vector_decimal
                                                        delta_x4 b
                                                        delta_x4_gradient
                                                        b_gradient of
                                                    | NONE => NONE
                                                    | SOME c =>
                                                      case
                                                        bounded_interval64_list_scale_decimal
                                                          u_reciprocal c of
                                                      | NONE => NONE
                                                      | SOME gradient_base =>
                                                        case
                                                          bounded_interval64_mul_decimal
                                                            root_four_x0
                                                            special_root_reciprocal of
                                                        | NONE => NONE
                                                        | SOME special_gradient =>
                                                          case
                                                            bounded_historical_replace_three
                                                              gradient_base
                                                              special_gradient of
                                                          | NONE => NONE
                                                          | SOME gradient =>
                                                            case
                                                              bounded_interval64_mul_decimal
                                                                (bounded_interval64_neg
                                                                  delta_x4)
                                                                b_reciprocal of
                                                            | NONE => NONE
                                                            | SOME quotient =>
                                                              case
                                                                bounded_interval64_atan_range_decimal
                                                                  quotient NONE NONE of
                                                              | NONE => NONE
                                                              | SOME angle =>
                                                                case
                                                                  bounded_interval64_add
                                                                    bounded_atan_pi_half_decimal
                                                                    angle of
                                                                | NONE => NONE
                                                                | SOME value =>
                                                                    SOME
                                                                      (value,gradient))
    | _ => NONE
End

Theorem bounded_interval64_list_pairwise_mul_decimal_length:
  !left right result.
    bounded_interval64_list_pairwise_mul_decimal left right = SOME result ==>
    LENGTH left = LENGTH right /\ LENGTH result = LENGTH left
Proof
  Induct
  >> Cases_on `right`
  >> simp [bounded_interval64_list_pairwise_mul_decimal_def]
  >> rw []
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> fs []
QED

Theorem bounded_historical_dihedral_first64_decimal_rejects_bad_length:
  LENGTH reciprocal_certificates <> 5 ==>
  bounded_historical_dihedral_first64_decimal environment root_delta
    root_four_x0 reciprocal_certificates = NONE
Proof
  rw [bounded_historical_dihedral_first64_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_historical_dihedral_first_decimal_closed_tests:
  let one = BoundedInterval64
    (BoundedSigned64 F 1000000000000w)
    (BoundedSigned64 F 1000000000000w) in
  let two = BoundedInterval64
    (BoundedSigned64 F 2000000000000w)
    (BoundedSigned64 F 2000000000000w) in
  let three = BoundedInterval64
    (BoundedSigned64 F 3000000000000w)
    (BoundedSigned64 F 3000000000000w) in
  bounded_interval64_list_pairwise_mul_decimal [one;two] [two;one] =
    SOME [two;two] /\
  bounded_historical_u_three_decimal one one one =
    SOME (three,[two;two;two]) /\
  bounded_historical_delta_x4_value_decimal (REPLICATE 6 one) = SOME one
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
