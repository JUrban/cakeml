(*****************************************************************************
 * Checked historical Flyspeck dihedral box jet at decimal scale 10^12.
 *
 * Shape, monotonicity, exact additions, and Hessian layout are reused from
 * the historical implementation.  Every rounded product, root/reciprocal
 * certificate, and arctangent is routed through the decimal engine.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralSecondDecimal
Ancestors
  compute_boundedHistoricalDihedralSecond
  compute_boundedHistoricalDihedralFirstDecimal
Libs
  bossLib preamble

Definition bounded_historical_delta_gradient_component_decimal_def:
  bounded_historical_delta_gradient_component_decimal
      (coordinate:num) environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      if coordinate = 0 then
        bounded_interval64_fused_products_decimal
          [(bounded_interval64_neg x0,x3);
           (bounded_interval64_neg x0,x3);
           (x1,x3);(x1,x4);(bounded_interval64_neg x1,x5);
           (x2,x3);(bounded_interval64_neg x2,x4);(x2,x5);
           (bounded_interval64_neg x3,x3);(x3,x4);(x3,x5)]
      else if coordinate = 1 then
        bounded_interval64_fused_products_decimal
          [(x0,x3);(x0,x4);(bounded_interval64_neg x0,x5);
           (bounded_interval64_neg x1,x4);
           (bounded_interval64_neg x1,x4);
           (bounded_interval64_neg x2,x3);(x2,x4);(x2,x5);
           (x3,x4);(bounded_interval64_neg x4,x4);(x4,x5)]
      else if coordinate = 2 then
        bounded_interval64_fused_products_decimal
          [(x0,x3);(bounded_interval64_neg x0,x4);(x0,x5);
           (bounded_interval64_neg x1,x3);(x1,x4);(x1,x5);
           (bounded_interval64_neg x2,x5);
           (bounded_interval64_neg x2,x5);
           (x3,x5);(x4,x5);(bounded_interval64_neg x5,x5)]
      else if coordinate = 3 then
        bounded_interval64_fused_products_decimal
          [(bounded_interval64_neg x0,x0);(x0,x1);(x0,x2);
           (bounded_interval64_neg x0,x3);
           (bounded_interval64_neg x0,x3);
           (x0,x4);(x0,x5);(bounded_interval64_neg x1,x2);
           (x1,x4);(x2,x5);(bounded_interval64_neg x4,x5)]
      else if coordinate = 4 then
        bounded_interval64_fused_products_decimal
          [(x0,x1);(bounded_interval64_neg x0,x2);(x0,x3);
           (bounded_interval64_neg x1,x1);(x1,x2);(x1,x3);
           (bounded_interval64_neg x1,x4);
           (bounded_interval64_neg x1,x4);
           (x1,x5);(x2,x5);(bounded_interval64_neg x3,x5)]
      else if coordinate = 5 then
        bounded_interval64_fused_products_decimal
          [(bounded_interval64_neg x0,x1);(x0,x2);(x0,x3);
           (x1,x2);(x1,x4);(bounded_interval64_neg x2,x2);
           (x2,x3);(x2,x4);
           (bounded_interval64_neg x2,x5);
           (bounded_interval64_neg x2,x5);
           (bounded_interval64_neg x3,x4)]
      else NONE
    | _ => NONE
End

Definition bounded_historical_delta_gradient_box_entry_decimal_def:
  bounded_historical_delta_gradient_box_entry_decimal environment derivatives
      (coordinate:num) =
    case bounded_historical_monotone_environment
      environment derivatives F of
    | NONE => NONE
    | SOME lower_environment =>
      case bounded_historical_monotone_environment
        environment derivatives T of
      | NONE => NONE
      | SOME upper_environment =>
        case bounded_historical_delta_gradient_component_decimal
          coordinate lower_environment of
        | NONE => NONE
        | SOME lower_value =>
          case bounded_historical_delta_gradient_component_decimal
            coordinate upper_environment of
          | NONE => NONE
          | SOME upper_value =>
              SOME (bounded_historical_extreme_interval
                lower_value upper_value)
End

Definition bounded_historical_delta_gradient_box_decimal_def:
  bounded_historical_delta_gradient_box_decimal environment [] [] = SOME [] /\
  bounded_historical_delta_gradient_box_decimal environment
      (coordinate::coordinates) (derivatives::derivative_rows) =
    (case bounded_historical_delta_gradient_box_entry_decimal
      environment derivatives coordinate of
    | NONE => NONE
    | SOME value =>
      case bounded_historical_delta_gradient_box_decimal
        environment coordinates derivative_rows of
      | NONE => NONE
      | SOME rest => SOME (value::rest)) /\
  bounded_historical_delta_gradient_box_decimal environment _ _ = NONE
End

Definition bounded_historical_delta_second_decimal_def:
  bounded_historical_delta_second_decimal environment =
    case bounded_delta64_hessian environment of
    | NONE => NONE
    | SOME hessian =>
      case bounded_hessian64_rows hessian of
      | NONE => NONE
      | SOME derivative_rows =>
        case bounded_historical_delta_gradient_box_decimal
          environment [0;1;2;3;4;5] derivative_rows of
        | NONE => NONE
        | SOME gradient =>
          case bounded_historical_monotone_environment
            environment gradient F of
          | NONE => NONE
          | SOME lower_environment =>
            case bounded_historical_monotone_environment
              environment gradient T of
            | NONE => NONE
            | SOME upper_environment =>
              case bounded_historical_delta64_value_decimal lower_environment of
              | NONE => NONE
              | SOME lower_value =>
                case bounded_historical_delta64_value_decimal upper_environment of
                | NONE => NONE
                | SOME upper_value =>
                    SOME
                      (bounded_historical_extreme_interval
                         lower_value upper_value,
                       gradient,hessian)
End

Definition bounded_historical_delta_x4_value_block_decimal_def:
  bounded_historical_delta_x4_value_block_decimal environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_interval64_sum
        [bounded_interval64_neg x0;x1;x2;
         bounded_interval64_neg x3;x4;x5] of
      | NONE => NONE
      | SOME linear =>
          bounded_interval64_fused_products_decimal
            [(bounded_interval64_neg x1,x2);
             (bounded_interval64_neg x0,x3);
             (x1,x4);(x2,x5);
             (bounded_interval64_neg x4,x5);
             (x0,linear)])
    | _ => NONE
End

Definition bounded_historical_delta_x4_hessian_decimal_def:
  bounded_historical_delta_x4_hessian_decimal =
    case bounded_historical_scale2 bounded_atan_one_decimal of
    | NONE => NONE
    | SOME two =>
        SOME
          [bounded_interval64_neg two;
           bounded_atan_one_decimal;bounded_atan_one_decimal;
           bounded_interval64_neg two;
           bounded_atan_one_decimal;bounded_atan_one_decimal;
           bounded_interval64_zero;
           bounded_interval64_neg bounded_atan_one_decimal;
           bounded_interval64_zero;bounded_atan_one_decimal;
           bounded_interval64_zero;
           bounded_interval64_zero;
           bounded_interval64_zero;bounded_interval64_zero;
           bounded_atan_one_decimal;
           bounded_interval64_zero;bounded_interval64_zero;
           bounded_interval64_zero;
           bounded_interval64_zero;
           bounded_interval64_neg bounded_atan_one_decimal;
           bounded_interval64_zero]
End

Definition bounded_historical_delta_x4_second_decimal_def:
  bounded_historical_delta_x4_second_decimal environment =
    case bounded_historical_delta_x4_gradient environment of
    | NONE => NONE
    | SOME gradient =>
      case bounded_historical_delta_x4_hessian_decimal of
      | NONE => NONE
      | SOME hessian =>
        case bounded_historical_monotone_environment
          environment gradient F of
        | NONE => NONE
        | SOME lower_environment =>
          case bounded_historical_monotone_environment
            environment gradient T of
          | NONE => NONE
          | SOME upper_environment =>
            case bounded_historical_delta_x4_value_block_decimal
              lower_environment of
            | NONE => NONE
            | SOME lower_value =>
              case bounded_historical_delta_x4_value_block_decimal
                upper_environment of
              | NONE => NONE
              | SOME upper_value =>
                  SOME
                    (bounded_historical_extreme_interval
                       lower_value upper_value,
                     gradient,hessian)
End

Definition bounded_historical_sqrt_hessian_decimal_def:
  bounded_historical_sqrt_hessian_decimal derivative logarithmic_derivative
      gradient [] [] = SOME [] /\
  bounded_historical_sqrt_hessian_decimal derivative logarithmic_derivative
      gradient [] (_::_) = NONE /\
  bounded_historical_sqrt_hessian_decimal derivative logarithmic_derivative
      gradient (_::_) [] = NONE /\
  bounded_historical_sqrt_hessian_decimal derivative logarithmic_derivative
      gradient ((row,column)::indices) (hessian_entry::hessian_entries) =
    (case bounded_interval64_nth gradient row of
    | NONE => NONE
    | SOME row_gradient =>
      case bounded_interval64_nth gradient column of
      | NONE => NONE
      | SOME column_gradient =>
        case bounded_interval64_mul_decimal logarithmic_derivative row_gradient of
        | NONE => NONE
        | SOME scaled_row =>
          case bounded_interval64_mul_decimal column_gradient scaled_row of
          | NONE => NONE
          | SOME outer =>
            case bounded_interval64_add outer hessian_entry of
            | NONE => NONE
            | SOME inside =>
              case bounded_interval64_mul_decimal derivative inside of
              | NONE => NONE
              | SOME value =>
                case bounded_historical_sqrt_hessian_decimal
                  derivative logarithmic_derivative gradient
                  indices hessian_entries of
                | NONE => NONE
                | SOME rest => SOME (value::rest))
End

Definition bounded_historical_sqrt_second_decimal_def:
  bounded_historical_sqrt_second_decimal value gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    if ¬bounded_interval64_positive_sqrt_certificate_decimal value root then NONE
    else
      case bounded_historical_scale2 root of
      | NONE => NONE
      | SOME twice_root =>
        if ¬bounded_interval64_positive_inv_certificate_decimal
          twice_root derivative_reciprocal then NONE
        else
          case bounded_historical_scale2 value of
          | NONE => NONE
          | SOME twice_value =>
            if ¬bounded_interval64_positive_inv_certificate_decimal
              twice_value logarithmic_reciprocal then NONE
            else
              case bounded_interval64_list_scale_decimal
                derivative_reciprocal gradient of
              | NONE => NONE
              | SOME result_gradient =>
                case bounded_historical_sqrt_hessian_decimal
                  derivative_reciprocal
                  (bounded_interval64_neg logarithmic_reciprocal)
                  gradient bounded_delta64_hessian_indices hessian of
                | NONE => NONE
                | SOME result_hessian =>
                    SOME (root,result_gradient,result_hessian)
End

Definition bounded_historical_b_hessian_decimal_def:
  bounded_historical_b_hessian_decimal root_delta two_over_root_four
      diagonal_reciprocal root_gradient base_hessian =
    case root_gradient of
    | g0::g1::g2::g3::g4::g5::[] =>
      (case base_hessian of
      | h00::h01::h02::h03::h04::h05::
        h11::h12::h13::h14::h15::
        h22::h23::h24::h25::
        h33::h34::h35::h44::h45::h55::[] =>
        (case bounded_interval64_mul_decimal g0 two_over_root_four of
        | NONE => NONE
        | SOME first_correction =>
          case bounded_historical_scale2 first_correction of
          | NONE => NONE
          | SOME twice_first_correction =>
            case bounded_interval64_mul_decimal root_delta two_over_root_four of
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
                  case bounded_interval64_add h00 diagonal_correction of
                  | NONE => NONE
                  | SOME r00 =>
                    case bounded_interval64_mul_decimal g1 two_over_root_four of
                    | NONE => NONE
                    | SOME c01 =>
                      case bounded_interval64_add h01 c01 of
                      | NONE => NONE
                      | SOME r01 =>
                        case bounded_interval64_mul_decimal g2 two_over_root_four of
                        | NONE => NONE
                        | SOME c02 =>
                          case bounded_interval64_add h02 c02 of
                          | NONE => NONE
                          | SOME r02 =>
                            case bounded_interval64_mul_decimal
                              g3 two_over_root_four of
                            | NONE => NONE
                            | SOME c03 =>
                              case bounded_interval64_add h03 c03 of
                              | NONE => NONE
                              | SOME r03 =>
                                case bounded_interval64_mul_decimal
                                  g4 two_over_root_four of
                                | NONE => NONE
                                | SOME c04 =>
                                  case bounded_interval64_add h04 c04 of
                                  | NONE => NONE
                                  | SOME r04 =>
                                    case bounded_interval64_mul_decimal
                                      g5 two_over_root_four of
                                    | NONE => NONE
                                    | SOME c05 =>
                                      case bounded_interval64_add h05 c05 of
                                      | NONE => NONE
                                      | SOME r05 =>
                                          SOME
                                            [r00;r01;r02;r03;r04;r05;
                                             h11;h12;h13;h14;h15;
                                             h22;h23;h24;h25;
                                             h33;h34;h35;h44;h45;h55])
      | _ => NONE)
    | _ => NONE
End

Definition bounded_historical_second_hessian_entry_decimal_def:
  bounded_historical_second_hessian_entry_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      (row:num) (column:num) delta_x4_hessian b_hessian =
    case bounded_interval64_nth delta_x4_gradient row of
    | NONE => NONE
    | SOME delta_x4_row =>
      case bounded_interval64_nth delta_x4_gradient column of
      | NONE => NONE
      | SOME delta_x4_column =>
        case bounded_interval64_nth b_gradient row of
        | NONE => NONE
        | SOME b_row =>
          case bounded_interval64_nth b_gradient column of
          | NONE => NONE
          | SOME b_column =>
            case bounded_interval64_nth result_gradient row of
            | NONE => NONE
            | SOME result_row =>
              case bounded_interval64_nth logarithmic_u_gradient column of
              | NONE => NONE
              | SOME logarithmic_column =>
                case bounded_interval64_mul_decimal b delta_x4_hessian of
                | NONE => NONE
                | SOME first_term =>
                  case bounded_interval64_mul_decimal delta_x4 b_hessian of
                  | NONE => NONE
                  | SOME final_term =>
                    case
                      (if row = column then
                         bounded_interval64_add
                           (bounded_interval64_neg first_term) final_term
                       else
                         case bounded_interval64_mul_decimal
                           delta_x4_row b_column of
                         | NONE => NONE
                         | SOME second_term =>
                           case bounded_interval64_mul_decimal
                             delta_x4_column b_row of
                           | NONE => NONE
                           | SOME third_term =>
                               bounded_interval64_sum
                                 [bounded_interval64_neg first_term;
                                  bounded_interval64_neg second_term;
                                  third_term;final_term]) of
                    | NONE => NONE
                    | SOME identity =>
                      case bounded_interval64_mul_decimal reciprocal_u identity of
                      | NONE => NONE
                      | SOME scaled_identity =>
                        case bounded_interval64_mul_decimal
                          result_row logarithmic_column of
                        | NONE => NONE
                        | SOME logarithmic_term =>
                            bounded_interval64_add scaled_identity
                              (bounded_interval64_neg logarithmic_term)
End

Definition bounded_historical_second_hessian_decimal_def:
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] [] [] = SOME [] /\
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] _ _ = NONE /\
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      _ [] _ = NONE /\
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      _ _ [] = NONE /\
  bounded_historical_second_hessian_decimal delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      ((row,column)::indices) (delta_entry::delta_entries)
      (b_entry::b_entries) =
    (case bounded_historical_second_hessian_entry_decimal
      delta_x4 b reciprocal_u delta_x4_gradient b_gradient
      result_gradient logarithmic_u_gradient row column
      delta_entry b_entry of
    | NONE => NONE
    | SOME value =>
      case bounded_historical_second_hessian_decimal
        delta_x4 b reciprocal_u delta_x4_gradient b_gradient
        result_gradient logarithmic_u_gradient indices
        delta_entries b_entries of
      | NONE => NONE
      | SOME rest => SOME (value::rest))
End

Definition bounded_historical_dihedral_second64_decimal_def:
  bounded_historical_dihedral_second64_decimal environment root_delta
      root_four_x0 reciprocal_certificates =
    case reciprocal_certificates of
    | root_derivative::root_logarithmic::root_four_reciprocal::
        diagonal_reciprocal::u_reciprocal::special_root_reciprocal::
        b_reciprocal::u126_reciprocal::u135_reciprocal::[] =>
      (case bounded_historical_delta_second_decimal environment of
      | NONE => NONE
      | SOME (delta_interval,delta_gradient,delta_hessian) =>
        case bounded_historical_sqrt_second_decimal
          delta_interval delta_gradient delta_hessian root_delta
          root_derivative root_logarithmic of
        | NONE => NONE
        | SOME (_,root_gradient,root_hessian) =>
          case bounded_historical_delta_x4_second_decimal environment of
          | NONE => NONE
          | SOME (delta_x4,delta_x4_gradient,delta_x4_hessian) =>
            case bounded_historical_u126_decimal environment of
            | NONE => NONE
            | SOME (u126,u126_gradient) =>
              case bounded_historical_u135_decimal environment of
              | NONE => NONE
              | SOME (u135,u135_gradient) =>
                case bounded_interval64_nth environment 0 of
                | NONE => NONE
                | SOME x0 =>
                  case bounded_interval64_scale4 x0 of
                  | NONE => NONE
                  | SOME four_x0 =>
                    if ¬bounded_interval64_positive_sqrt_certificate_decimal
                      four_x0 root_four_x0 then NONE
                    else if ¬bounded_interval64_positive_inv_certificate_decimal
                      root_four_x0 root_four_reciprocal then NONE
                    else
                      case bounded_historical_scale2 x0 of
                      | NONE => NONE
                      | SOME twice_x0 =>
                        if ¬bounded_interval64_positive_inv_certificate_decimal
                          twice_x0 diagonal_reciprocal then NONE
                        else
                          case bounded_interval64_mul_decimal
                            root_delta root_four_x0 of
                          | NONE => NONE
                          | SOME b =>
                            if ¬bounded_interval64_positive_inv_certificate_decimal
                              b b_reciprocal then NONE
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
                                      root_delta two_over_root_four of
                                    | NONE => NONE
                                    | SOME b_correction =>
                                      case bounded_interval64_list_add_at
                                        b_correction 0 b_gradient_base of
                                      | NONE => NONE
                                      | SOME b_gradient =>
                                        case bounded_interval64_list_scale_decimal
                                          root_four_x0 root_hessian of
                                        | NONE => NONE
                                        | SOME b_hessian_base =>
                                          case bounded_historical_b_hessian_decimal
                                            root_delta two_over_root_four
                                            diagonal_reciprocal root_gradient
                                            b_hessian_base of
                                          | NONE => NONE
                                          | SOME b_hessian =>
                                            case bounded_historical_c_vector_decimal
                                              delta_x4 b delta_x4_gradient
                                              b_gradient of
                                            | NONE => NONE
                                            | SOME c =>
                                              case bounded_interval64_mul_decimal
                                                u126 u135 of
                                              | NONE => NONE
                                              | SOME u_product =>
                                                if
                                                  ¬bounded_interval64_positive_inv_certificate_decimal
                                                    u_product u_reciprocal
                                                then NONE
                                                else if
                                                  ¬bounded_interval64_positive_inv_certificate_decimal
                                                    u126 u126_reciprocal
                                                then NONE
                                                else if
                                                  ¬bounded_interval64_positive_inv_certificate_decimal
                                                    u135 u135_reciprocal
                                                then NONE
                                                else
                                                  case
                                                    bounded_interval64_list_scale_decimal
                                                      u_reciprocal c of
                                                  | NONE => NONE
                                                  | SOME gradient_base =>
                                                    case
                                                      bounded_historical_scale2
                                                        root_delta of
                                                    | NONE => NONE
                                                    | SOME twice_root_delta =>
                                                      if
                                                        ¬bounded_interval64_positive_inv_certificate_decimal
                                                          twice_root_delta
                                                          special_root_reciprocal
                                                      then NONE
                                                      else
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
                                                              bounded_interval64_list_scale_decimal
                                                                u126_reciprocal
                                                                u126_gradient of
                                                            | NONE => NONE
                                                            | SOME logarithmic_126 =>
                                                              case
                                                                bounded_interval64_list_scale_decimal
                                                                  u135_reciprocal
                                                                  u135_gradient of
                                                              | NONE => NONE
                                                              | SOME logarithmic_135 =>
                                                                case
                                                                  bounded_interval64_list_add
                                                                    logarithmic_126
                                                                    logarithmic_135 of
                                                                | NONE => NONE
                                                                | SOME logarithmic_u_gradient =>
                                                                  case
                                                                    bounded_historical_second_hessian_decimal
                                                                      delta_x4 b
                                                                      u_reciprocal
                                                                      delta_x4_gradient
                                                                      b_gradient
                                                                      gradient
                                                                      logarithmic_u_gradient
                                                                      bounded_delta64_hessian_indices
                                                                      delta_x4_hessian
                                                                      b_hessian of
                                                                  | NONE => NONE
                                                                  | SOME hessian =>
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
                                                                            bounded_historical_pi_half_decimal
                                                                            angle of
                                                                        | NONE => NONE
                                                                        | SOME value =>
                                                                            SOME
                                                                              (value,gradient,hessian))
    | _ => NONE
End

Theorem bounded_historical_dihedral_second64_decimal_rejects_bad_length:
  LENGTH reciprocal_certificates <> 9 ==>
  bounded_historical_dihedral_second64_decimal environment root_delta
    root_four_x0 reciprocal_certificates = NONE
Proof
  rw [bounded_historical_dihedral_second64_decimal_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_historical_delta_x4_hessian_decimal_length:
  bounded_historical_delta_x4_hessian_decimal = SOME hessian ==>
  LENGTH hessian = 21
Proof
  rw [bounded_historical_delta_x4_hessian_decimal_def,
      compute_boundedHistoricalDihedralFirstTheory.bounded_historical_scale2_def,
      compute_boundedAtanDecimalTheory.bounded_atan_one_decimal_def]
  >> every_case_tac
  >> gvs []
QED

val _ = export_theory ();
