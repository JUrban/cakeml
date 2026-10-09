(*****************************************************************************
 * Checked scale-2^40 historical Flyspeck dihedral center jet.
 *
 * Square roots and reciprocals are supplied by untrusted preparation.  The
 * existing exact word certificates authenticate them before use; every
 * polynomial, U-bound, quotient, atan, value, and derivative operation is
 * then recomputed with checked bounded arithmetic.  This is the first half
 * of the matched historical value/gradient/Hessian operation.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralFirst
Ancestors
  compute_boundedHistoricalDelta compute_boundedAtan
Libs
  bossLib preamble

Definition bounded_historical_scale2_def:
  bounded_historical_scale2 value = bounded_interval64_add value value
End

Definition bounded_historical_point_lower_def:
  bounded_historical_point_lower value =
    BoundedInterval64
      (bounded_interval64_lower value) (bounded_interval64_lower value)
End

Definition bounded_historical_point_upper_def:
  bounded_historical_point_upper value =
    BoundedInterval64
      (bounded_interval64_upper value) (bounded_interval64_upper value)
End

Definition bounded_historical_u_upper_negative_def:
  bounded_historical_u_upper_negative value gradient =
    if bounded_signed64_nonnegative (bounded_interval64_lower gradient)
    then bounded_historical_point_upper value
    else bounded_historical_point_lower value
End

Definition bounded_historical_u_upper_positive_def:
  bounded_historical_u_upper_positive value gradient =
    if bounded_signed64_nonpositive (bounded_interval64_upper gradient)
    then bounded_historical_point_lower value
    else bounded_historical_point_upper value
End

Definition bounded_historical_u_lower_negative_def:
  bounded_historical_u_lower_negative value gradient =
    if bounded_signed64_nonnegative (bounded_interval64_lower gradient)
    then bounded_historical_point_lower value
    else bounded_historical_point_upper value
End

Definition bounded_historical_u_lower_positive_def:
  bounded_historical_u_lower_positive value gradient =
    if bounded_signed64_nonpositive (bounded_interval64_upper gradient)
    then bounded_historical_point_upper value
    else bounded_historical_point_lower value
End

Definition bounded_historical_u_block_def:
  bounded_historical_u_block n0 n1 n2 p0 p1 p2 =
    bounded_interval64_fused_products
      [(bounded_interval64_neg n0,n0);
       (bounded_interval64_neg n1,n1);
       (bounded_interval64_neg n2,n2);
       (p0,p1);(p0,p1);
       (p1,p2);(p1,p2);
       (p2,p0);(p2,p0)]
End

Definition bounded_historical_u_three_def:
  bounded_historical_u_three x0 x1 x2 =
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
            case bounded_interval64_sum [x0;x1;bounded_interval64_neg x2] of
            | NONE => NONE
            | SOME g2_half =>
              case bounded_historical_scale2 g2_half of
              | NONE => NONE
              | SOME g2 =>
                case bounded_historical_u_block
                  (bounded_historical_u_lower_negative x0 g0)
                  (bounded_historical_u_lower_negative x1 g1)
                  (bounded_historical_u_lower_negative x2 g2)
                  (bounded_historical_u_lower_positive x0 g0)
                  (bounded_historical_u_lower_positive x1 g1)
                  (bounded_historical_u_lower_positive x2 g2) of
                | NONE => NONE
                | SOME lower_value =>
                  case bounded_historical_u_block
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

Definition bounded_historical_u126_def:
  bounded_historical_u126 environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_historical_u_three x0 x1 x5 of
      | NONE => NONE
      | SOME (value,g0::g1::g2::[]) =>
          SOME (value,
            [g0;g1;bounded_interval64_zero;bounded_interval64_zero;
             bounded_interval64_zero;g2])
      | SOME _ => NONE
    | _ => NONE
End

Definition bounded_historical_u135_def:
  bounded_historical_u135 environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_historical_u_three x0 x2 x4 of
      | NONE => NONE
      | SOME (value,g0::g1::g2::[]) =>
          SOME (value,
            [g0;bounded_interval64_zero;g1;bounded_interval64_zero;
             g2;bounded_interval64_zero])
      | SOME _ => NONE
    | _ => NONE
End

Definition bounded_historical_delta_x4_value_def:
  bounded_historical_delta_x4_value environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_interval64_sum
        [bounded_interval64_neg x0;x1;x2;
         bounded_interval64_neg x3;x4;x5] of
      | NONE => NONE
      | SOME linear =>
        case bounded_interval64_mul x1 x2 of
        | NONE => NONE
        | SOME p12 =>
          case bounded_interval64_mul x0 x3 of
          | NONE => NONE
          | SOME p03 =>
            case bounded_interval64_mul x1 x4 of
            | NONE => NONE
            | SOME p14 =>
              case bounded_interval64_mul x2 x5 of
              | NONE => NONE
              | SOME p25 =>
                case bounded_interval64_mul x4 x5 of
                | NONE => NONE
                | SOME p45 =>
                  case bounded_interval64_mul x0 linear of
                  | NONE => NONE
                  | SOME p0l =>
                      bounded_interval64_sum
                        [bounded_interval64_neg p12;
                         bounded_interval64_neg p03;p14;p25;
                         bounded_interval64_neg p45;p0l]
    | _ => NONE
End

Definition bounded_historical_delta_x4_gradient_def:
  bounded_historical_delta_x4_gradient environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      case bounded_interval64_sum
        [bounded_interval64_neg x0;bounded_interval64_neg x0;
         x1;x2;bounded_interval64_neg x3;bounded_interval64_neg x3;x4;x5] of
      | NONE => NONE
      | SOME g0 =>
        case bounded_interval64_sum [x0;bounded_interval64_neg x2;x4] of
        | NONE => NONE
        | SOME g1 =>
          case bounded_interval64_sum [x0;bounded_interval64_neg x1;x5] of
          | NONE => NONE
          | SOME g2 =>
            case bounded_historical_scale2 (bounded_interval64_neg x0) of
            | NONE => NONE
            | SOME g3 =>
              case bounded_interval64_sum [x0;x1;bounded_interval64_neg x5] of
              | NONE => NONE
              | SOME g4 =>
                case bounded_interval64_sum
                  [x0;x2;bounded_interval64_neg x4] of
                | NONE => NONE
                | SOME g5 => SOME [g0;g1;g2;g3;g4;g5]
    | _ => NONE
End

Definition bounded_historical_c_vector_def:
  bounded_historical_c_vector delta_x4 b [] [] = SOME [] ∧
  bounded_historical_c_vector delta_x4 b
      (delta_gradient::delta_rest) (b_gradient::b_rest) =
    (case bounded_interval64_mul delta_gradient b of
     | NONE => NONE
     | SOME first =>
       case bounded_interval64_mul delta_x4 b_gradient of
       | NONE => NONE
       | SOME second =>
         case bounded_interval64_add (bounded_interval64_neg first) second of
         | NONE => NONE
         | SOME value =>
           case bounded_historical_c_vector
             delta_x4 b delta_rest b_rest of
           | NONE => NONE
           | SOME rest => SOME (value::rest)) ∧
  bounded_historical_c_vector delta_x4 b _ _ = NONE
End

Definition bounded_historical_replace_three_def:
  bounded_historical_replace_three values replacement =
    case values of
    | v0::v1::v2::v3::v4::v5::[] =>
        SOME [v0;v1;v2;replacement;v4;v5]
    | _ => NONE
End

Definition bounded_historical_dihedral_first64_def:
  bounded_historical_dihedral_first64 environment root_delta root_four_x0
      reciprocal_certificates =
    case reciprocal_certificates of
    | root_derivative::root_four_reciprocal::u_reciprocal::
        special_root_reciprocal::b_reciprocal::[] =>
      case bounded_delta64_value environment of
      | NONE => NONE
      | SOME delta =>
        if ¬bounded_interval64_sqrt_certificate delta root_delta then NONE
        else
          case bounded_interval64_nth environment 0 of
          | NONE => NONE
          | SOME x0 =>
            case bounded_interval64_scale4 x0 of
            | NONE => NONE
            | SOME four_x0 =>
              if ¬bounded_interval64_sqrt_certificate
                  four_x0 root_four_x0 then NONE
              else
                case bounded_historical_scale2 root_delta of
                | NONE => NONE
                | SOME twice_root_delta =>
                  if ¬bounded_interval64_inv_certificate
                      twice_root_delta root_derivative then NONE
                  else if ¬bounded_interval64_inv_certificate
                      twice_root_delta special_root_reciprocal then NONE
                  else if ¬bounded_interval64_inv_certificate
                      root_four_x0 root_four_reciprocal then NONE
                  else
                    case bounded_delta64_pair_products environment of
                    | NONE => NONE
                    | SOME delta_products =>
                      case bounded_delta64_gradient_from_products
                        delta_products of
                      | NONE => NONE
                      | SOME delta_gradient =>
                        case bounded_interval64_list_scale
                          root_derivative delta_gradient of
                        | NONE => NONE
                        | SOME root_gradient =>
                          case bounded_historical_delta_x4_value environment of
                          | NONE => NONE
                          | SOME delta_x4 =>
                            case bounded_historical_delta_x4_gradient
                              environment of
                            | NONE => NONE
                            | SOME delta_x4_gradient =>
                              case bounded_historical_u126 environment of
                              | NONE => NONE
                              | SOME (u126,u126_gradient) =>
                                case bounded_historical_u135 environment of
                                | NONE => NONE
                                | SOME (u135,u135_gradient) =>
                                  case bounded_interval64_mul
                                    root_delta root_four_x0 of
                                  | NONE => NONE
                                  | SOME b =>
                                    if ¬bounded_interval64_inv_certificate
                                        b b_reciprocal then NONE
                                    else
                                      case bounded_interval64_mul u126 u135 of
                                      | NONE => NONE
                                      | SOME u_product =>
                                        if ¬bounded_interval64_inv_certificate
                                            u_product u_reciprocal then NONE
                                        else
                                          case bounded_historical_scale2
                                            bounded_atan_one of
                                          | NONE => NONE
                                          | SOME two =>
                                            case bounded_interval64_mul two
                                              root_four_reciprocal of
                                            | NONE => NONE
                                            | SOME two_over_root_four =>
                                              case bounded_interval64_list_scale
                                                root_four_x0 root_gradient of
                                              | NONE => NONE
                                              | SOME b_gradient_base =>
                                                case bounded_interval64_mul
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
                                                      bounded_historical_c_vector
                                                        delta_x4 b
                                                        delta_x4_gradient
                                                        b_gradient of
                                                    | NONE => NONE
                                                    | SOME c =>
                                                      case
                                                        bounded_interval64_list_scale
                                                          u_reciprocal c of
                                                      | NONE => NONE
                                                      | SOME gradient_base =>
                                                        case
                                                          bounded_interval64_mul
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
                                                              bounded_interval64_mul
                                                                (bounded_interval64_neg
                                                                  delta_x4)
                                                                b_reciprocal of
                                                            | NONE => NONE
                                                            | SOME quotient =>
                                                              case
                                                                bounded_interval64_atan_range
                                                                  quotient NONE NONE of
                                                              | NONE => NONE
                                                              | SOME angle =>
                                                                case
                                                                  bounded_interval64_add
                                                                    bounded_atan_pi_half
                                                                    angle of
                                                                | NONE => NONE
                                                                | SOME value =>
                                                                    SOME
                                                                      (value,gradient)
    | _ => NONE
End

val _ = export_theory ();
