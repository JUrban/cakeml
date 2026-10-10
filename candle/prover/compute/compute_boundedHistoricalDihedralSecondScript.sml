(*****************************************************************************
 * Checked scale-2^40 historical Flyspeck dihedral box jet.
 *
 * This is the matched second-order half of the native historical operation:
 * sign-directed delta and delta_x4 bounds, supplied-but-checked square roots
 * and reciprocals, and the complete six-gradient/21-Hessian result.
 *****************************************************************************)
Theory compute_boundedHistoricalDihedralSecond
Ancestors
  compute_boundedHistoricalDihedralFirst
Libs
  bossLib preamble intLib

Definition bounded_historical_extreme_interval_def:
  bounded_historical_extreme_interval lower_value upper_value =
    BoundedInterval64
      (bounded_interval64_lower lower_value)
      (bounded_interval64_upper upper_value)
End

Definition bounded_historical_monotone_coordinate_def:
  bounded_historical_monotone_coordinate value derivative upper =
    if bounded_signed64_nonnegative (bounded_interval64_lower derivative) then
      if upper then bounded_historical_point_upper value
      else bounded_historical_point_lower value
    else if bounded_signed64_nonpositive
      (bounded_interval64_upper derivative) then
      if upper then bounded_historical_point_lower value
      else bounded_historical_point_upper value
    else value
End

Definition bounded_historical_monotone_environment_def:
  bounded_historical_monotone_environment [] [] upper = SOME [] ∧
  bounded_historical_monotone_environment (value::values)
      (derivative::derivatives) upper =
    (case bounded_historical_monotone_environment
      values derivatives upper of
    | NONE => NONE
    | SOME rest =>
        SOME
          (bounded_historical_monotone_coordinate
             value derivative upper::rest)) ∧
  bounded_historical_monotone_environment _ _ upper = NONE
End

Definition bounded_interval64_subinterval_def:
  bounded_interval64_subinterval inner outer ⇔
    bounded_signed64_to_int (bounded_interval64_lower outer) ≤
      bounded_signed64_to_int (bounded_interval64_lower inner) ∧
    bounded_signed64_to_int (bounded_interval64_upper inner) ≤
      bounded_signed64_to_int (bounded_interval64_upper outer)
End

Definition bounded_historical_monotone_exact_def:
  bounded_historical_monotone_exact value derivative upper original =
    if bounded_signed64_nonnegative
         (bounded_interval64_lower derivative) then
      if upper then
        bounded_signed64_to_int (bounded_interval64_upper value)
      else bounded_signed64_to_int (bounded_interval64_lower value)
    else if bounded_signed64_nonpositive
      (bounded_interval64_upper derivative) then
      if upper then
        bounded_signed64_to_int (bounded_interval64_lower value)
      else bounded_signed64_to_int (bounded_interval64_upper value)
    else original
End

Definition bounded_historical_monotone_exact_environment_def:
  bounded_historical_monotone_exact_environment [] [] upper [] = [] ∧
  bounded_historical_monotone_exact_environment (value::values)
      (derivative::derivatives) upper (original::originals) =
    bounded_historical_monotone_exact value derivative upper original ::
      bounded_historical_monotone_exact_environment
        values derivatives upper originals ∧
  bounded_historical_monotone_exact_environment _ _ upper _ = []
End

Definition bounded_historical_delta_gradient_value_def:
  bounded_historical_delta_gradient_value (coordinate:num)
      (v0:int) v1 v2 v3 v4 v5 =
    if coordinate = 0 then
      (-v0) * v3 + (-v0) * v3 +
      v1 * v3 + v1 * v4 + (-v1) * v5 +
      v2 * v3 + (-v2) * v4 + v2 * v5 +
      (-v3) * v3 + v3 * v4 + v3 * v5
    else if coordinate = 1 then
      v0 * v3 + v0 * v4 + (-v0) * v5 +
      (-v1) * v4 + (-v1) * v4 +
      (-v2) * v3 + v2 * v4 + v2 * v5 +
      v3 * v4 + (-v4) * v4 + v4 * v5
    else if coordinate = 2 then
      v0 * v3 + (-v0) * v4 + v0 * v5 +
      (-v1) * v3 + v1 * v4 + v1 * v5 +
      (-v2) * v5 + (-v2) * v5 +
      v3 * v5 + v4 * v5 + (-v5) * v5
    else if coordinate = 3 then
      (-v0) * v0 + v0 * v1 + v0 * v2 +
      (-v0) * v3 + (-v0) * v3 + v0 * v4 + v0 * v5 +
      (-v1) * v2 + v1 * v4 + v2 * v5 + (-v4) * v5
    else if coordinate = 4 then
      v0 * v1 + (-v0) * v2 + v0 * v3 +
      (-v1) * v1 + v1 * v2 + v1 * v3 +
      (-v1) * v4 + (-v1) * v4 +
      v1 * v5 + v2 * v5 + (-v3) * v5
    else if coordinate = 5 then
      (-v0) * v1 + v0 * v2 + v0 * v3 +
      v1 * v2 + v1 * v4 + (-v2) * v2 +
      v2 * v3 + v2 * v4 +
      (-v2) * v5 + (-v2) * v5 + (-v3) * v4
    else 0
End

Definition bounded_historical_delta_hessian_value_def:
  bounded_historical_delta_hessian_value (row:num) (column:num)
      (v0:int) v1 v2 v3 v4 v5 =
    EL column
      (EL row (bounded_delta_hessian_value_matrix v0 v1 v2 v3 v4 v5))
End

Definition bounded_historical_delta_gradient_component_def:
  bounded_historical_delta_gradient_component (coordinate:num) environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      if coordinate = 0 then
        bounded_interval64_fused_products
          [(bounded_interval64_neg x0,x3);
           (bounded_interval64_neg x0,x3);
           (x1,x3);(x1,x4);(bounded_interval64_neg x1,x5);
           (x2,x3);(bounded_interval64_neg x2,x4);(x2,x5);
           (bounded_interval64_neg x3,x3);(x3,x4);(x3,x5)]
      else if coordinate = 1 then
        bounded_interval64_fused_products
          [(x0,x3);(x0,x4);(bounded_interval64_neg x0,x5);
           (bounded_interval64_neg x1,x4);
           (bounded_interval64_neg x1,x4);
           (bounded_interval64_neg x2,x3);(x2,x4);(x2,x5);
           (x3,x4);(bounded_interval64_neg x4,x4);(x4,x5)]
      else if coordinate = 2 then
        bounded_interval64_fused_products
          [(x0,x3);(bounded_interval64_neg x0,x4);(x0,x5);
           (bounded_interval64_neg x1,x3);(x1,x4);(x1,x5);
           (bounded_interval64_neg x2,x5);
           (bounded_interval64_neg x2,x5);
           (x3,x5);(x4,x5);(bounded_interval64_neg x5,x5)]
      else if coordinate = 3 then
        bounded_interval64_fused_products
          [(bounded_interval64_neg x0,x0);(x0,x1);(x0,x2);
           (bounded_interval64_neg x0,x3);
           (bounded_interval64_neg x0,x3);
           (x0,x4);(x0,x5);(bounded_interval64_neg x1,x2);
           (x1,x4);(x2,x5);(bounded_interval64_neg x4,x5)]
      else if coordinate = 4 then
        bounded_interval64_fused_products
          [(x0,x1);(bounded_interval64_neg x0,x2);(x0,x3);
           (bounded_interval64_neg x1,x1);(x1,x2);(x1,x3);
           (bounded_interval64_neg x1,x4);
           (bounded_interval64_neg x1,x4);
           (x1,x5);(x2,x5);(bounded_interval64_neg x3,x5)]
      else if coordinate = 5 then
        bounded_interval64_fused_products
          [(bounded_interval64_neg x0,x1);(x0,x2);(x0,x3);
           (x1,x2);(x1,x4);(bounded_interval64_neg x2,x2);
           (x2,x3);(x2,x4);
           (bounded_interval64_neg x2,x5);
           (bounded_interval64_neg x2,x5);
           (bounded_interval64_neg x3,x4)]
      else NONE
    | _ => NONE
End

Definition bounded_historical_delta_gradient_box_entry_def:
  bounded_historical_delta_gradient_box_entry environment derivatives
      (coordinate:num) =
    case bounded_historical_monotone_environment
      environment derivatives F of
    | NONE => NONE
    | SOME lower_environment =>
      case bounded_historical_monotone_environment
        environment derivatives T of
      | NONE => NONE
      | SOME upper_environment =>
        case bounded_historical_delta_gradient_component
          coordinate lower_environment of
        | NONE => NONE
        | SOME lower_value =>
          case bounded_historical_delta_gradient_component
            coordinate upper_environment of
          | NONE => NONE
          | SOME upper_value =>
              SOME (bounded_historical_extreme_interval
                lower_value upper_value)
End

Definition bounded_historical_delta_gradient_box_def:
  bounded_historical_delta_gradient_box environment [] [] = SOME [] ∧
  bounded_historical_delta_gradient_box environment
      (coordinate::coordinates) (derivatives::derivative_rows) =
    (case bounded_historical_delta_gradient_box_entry
      environment derivatives coordinate of
    | NONE => NONE
    | SOME value =>
      case bounded_historical_delta_gradient_box
        environment coordinates derivative_rows of
      | NONE => NONE
      | SOME rest => SOME (value::rest)) ∧
  bounded_historical_delta_gradient_box environment _ _ = NONE
End

Definition bounded_historical_delta_second_def:
  bounded_historical_delta_second environment =
    case bounded_delta64_hessian environment of
    | NONE => NONE
    | SOME hessian =>
      case bounded_hessian64_rows hessian of
      | NONE => NONE
      | SOME derivative_rows =>
        case bounded_historical_delta_gradient_box
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
              case bounded_historical_delta64_value lower_environment of
              | NONE => NONE
              | SOME lower_value =>
                case bounded_historical_delta64_value upper_environment of
                | NONE => NONE
                | SOME upper_value =>
                    SOME
                      (bounded_historical_extreme_interval
                         lower_value upper_value,
                       gradient,hessian)
End

Definition bounded_historical_delta_x4_value_block_def:
  bounded_historical_delta_x4_value_block environment =
    case environment of
    | x0::x1::x2::x3::x4::x5::[] =>
      (case bounded_interval64_sum
        [bounded_interval64_neg x0;x1;x2;
         bounded_interval64_neg x3;x4;x5] of
      | NONE => NONE
      | SOME linear =>
          bounded_interval64_fused_products
            [(bounded_interval64_neg x1,x2);
             (bounded_interval64_neg x0,x3);
             (x1,x4);(x2,x5);
             (bounded_interval64_neg x4,x5);
             (x0,linear)])
    | _ => NONE
End

Definition bounded_historical_delta_x4_exact_value_def:
  bounded_historical_delta_x4_exact_value
      (v0:int) v1 v2 v3 v4 v5 =
    (-v1) * v2 + (-v0) * v3 + v1 * v4 + v2 * v5 +
    (-v4) * v5 + v0 * ((-v0) + v1 + v2 + (-v3) + v4 + v5)
End

Definition bounded_historical_delta_x4_hessian_def:
  bounded_historical_delta_x4_hessian =
    case bounded_historical_scale2 bounded_atan_one of
    | NONE => NONE
    | SOME two =>
        SOME
          [bounded_interval64_neg two;
           bounded_atan_one;bounded_atan_one;
           bounded_interval64_neg two;
           bounded_atan_one;bounded_atan_one;
           bounded_interval64_zero;
           bounded_interval64_neg bounded_atan_one;
           bounded_interval64_zero;bounded_atan_one;
           bounded_interval64_zero;
           bounded_interval64_zero;
           bounded_interval64_zero;bounded_interval64_zero;
           bounded_atan_one;
           bounded_interval64_zero;bounded_interval64_zero;
           bounded_interval64_zero;
           bounded_interval64_zero;
           bounded_interval64_neg bounded_atan_one;
           bounded_interval64_zero]
End

Definition bounded_historical_delta_x4_second_def:
  bounded_historical_delta_x4_second environment =
    case bounded_historical_delta_x4_gradient environment of
    | NONE => NONE
    | SOME gradient =>
      case bounded_historical_delta_x4_hessian of
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
            case bounded_historical_delta_x4_value_block
              lower_environment of
            | NONE => NONE
            | SOME lower_value =>
              case bounded_historical_delta_x4_value_block
                upper_environment of
              | NONE => NONE
              | SOME upper_value =>
                  SOME
                    (bounded_historical_extreme_interval
                       lower_value upper_value,
                     gradient,hessian)
End

Definition bounded_historical_sqrt_hessian_def:
  bounded_historical_sqrt_hessian derivative logarithmic_derivative
      gradient [] [] = SOME [] ∧
  bounded_historical_sqrt_hessian derivative logarithmic_derivative
      gradient [] (_::_) = NONE ∧
  bounded_historical_sqrt_hessian derivative logarithmic_derivative
      gradient (_::_) [] = NONE ∧
  bounded_historical_sqrt_hessian derivative logarithmic_derivative gradient
      ((row,column)::indices) (hessian_entry::hessian_entries) =
    (case bounded_interval64_nth gradient row of
    | NONE => NONE
    | SOME row_gradient =>
      case bounded_interval64_nth gradient column of
      | NONE => NONE
      | SOME column_gradient =>
        case bounded_interval64_mul logarithmic_derivative row_gradient of
        | NONE => NONE
        | SOME scaled_row =>
          case bounded_interval64_mul column_gradient scaled_row of
          | NONE => NONE
          | SOME outer =>
            case bounded_interval64_add outer hessian_entry of
            | NONE => NONE
            | SOME inside =>
              case bounded_interval64_mul derivative inside of
              | NONE => NONE
              | SOME value =>
                case bounded_historical_sqrt_hessian
                  derivative logarithmic_derivative gradient
                  indices hessian_entries of
                | NONE => NONE
                | SOME rest => SOME (value::rest))
End

Definition bounded_historical_sqrt_second_def:
  bounded_historical_sqrt_second value gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    if ¬bounded_interval64_sqrt_certificate value root then NONE
    else
      case bounded_historical_scale2 root of
      | NONE => NONE
      | SOME twice_root =>
        if ¬bounded_interval64_inv_certificate
          twice_root derivative_reciprocal then NONE
        else
          case bounded_historical_scale2 value of
          | NONE => NONE
          | SOME twice_value =>
            if ¬bounded_interval64_inv_certificate
              twice_value logarithmic_reciprocal then NONE
            else
              case bounded_interval64_list_scale
                derivative_reciprocal gradient of
              | NONE => NONE
              | SOME result_gradient =>
                case bounded_historical_sqrt_hessian
                  derivative_reciprocal
                  (bounded_interval64_neg logarithmic_reciprocal)
                  gradient bounded_delta64_hessian_indices hessian of
                | NONE => NONE
                | SOME result_hessian =>
                    SOME (root,result_gradient,result_hessian)
End

Definition bounded_historical_b_hessian_def:
  bounded_historical_b_hessian root_delta two_over_root_four
      diagonal_reciprocal root_gradient base_hessian =
    case root_gradient of
    | g0::g1::g2::g3::g4::g5::[] =>
      (case base_hessian of
      | h00::h01::h02::h03::h04::h05::
        h11::h12::h13::h14::h15::
        h22::h23::h24::h25::
        h33::h34::h35::h44::h45::h55::[] =>
        (case bounded_interval64_mul g0 two_over_root_four of
        | NONE => NONE
        | SOME first_correction =>
          case bounded_historical_scale2 first_correction of
          | NONE => NONE
          | SOME twice_first_correction =>
            case bounded_interval64_mul root_delta two_over_root_four of
            | NONE => NONE
            | SOME diagonal_numerator =>
              case bounded_interval64_mul
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
                    case bounded_interval64_mul g1 two_over_root_four of
                    | NONE => NONE
                    | SOME c01 =>
                      case bounded_interval64_add h01 c01 of
                      | NONE => NONE
                      | SOME r01 =>
                        case bounded_interval64_mul g2 two_over_root_four of
                        | NONE => NONE
                        | SOME c02 =>
                          case bounded_interval64_add h02 c02 of
                          | NONE => NONE
                          | SOME r02 =>
                            case bounded_interval64_mul
                              g3 two_over_root_four of
                            | NONE => NONE
                            | SOME c03 =>
                              case bounded_interval64_add h03 c03 of
                              | NONE => NONE
                              | SOME r03 =>
                                case bounded_interval64_mul
                                  g4 two_over_root_four of
                                | NONE => NONE
                                | SOME c04 =>
                                  case bounded_interval64_add h04 c04 of
                                  | NONE => NONE
                                  | SOME r04 =>
                                    case bounded_interval64_mul
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

Definition bounded_historical_second_hessian_entry_def:
  bounded_historical_second_hessian_entry delta_x4 b reciprocal_u
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
                case bounded_interval64_mul b delta_x4_hessian of
                | NONE => NONE
                | SOME first_term =>
                  case bounded_interval64_mul delta_x4 b_hessian of
                  | NONE => NONE
                  | SOME final_term =>
                    case
                      (if row = column then
                         bounded_interval64_add
                           (bounded_interval64_neg first_term) final_term
                       else
                         case bounded_interval64_mul
                           delta_x4_row b_column of
                         | NONE => NONE
                         | SOME second_term =>
                           case bounded_interval64_mul
                             delta_x4_column b_row of
                           | NONE => NONE
                           | SOME third_term =>
                               bounded_interval64_sum
                                 [bounded_interval64_neg first_term;
                                  bounded_interval64_neg second_term;
                                  third_term;final_term]) of
                    | NONE => NONE
                    | SOME identity =>
                      case bounded_interval64_mul reciprocal_u identity of
                      | NONE => NONE
                      | SOME scaled_identity =>
                        case bounded_interval64_mul
                          result_row logarithmic_column of
                        | NONE => NONE
                        | SOME logarithmic_term =>
                            bounded_interval64_add scaled_identity
                              (bounded_interval64_neg logarithmic_term)
End

Definition bounded_historical_second_hessian_def:
  bounded_historical_second_hessian delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] [] [] = SOME [] ∧
  bounded_historical_second_hessian delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      [] _ _ = NONE ∧
  bounded_historical_second_hessian delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      _ [] _ = NONE ∧
  bounded_historical_second_hessian delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      _ _ [] = NONE ∧
  bounded_historical_second_hessian delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      ((row,column)::indices) (delta_entry::delta_entries)
      (b_entry::b_entries) =
    (case bounded_historical_second_hessian_entry
      delta_x4 b reciprocal_u delta_x4_gradient b_gradient
      result_gradient logarithmic_u_gradient row column
      delta_entry b_entry of
    | NONE => NONE
    | SOME value =>
      case bounded_historical_second_hessian
        delta_x4 b reciprocal_u delta_x4_gradient b_gradient
        result_gradient logarithmic_u_gradient indices
        delta_entries b_entries of
      | NONE => NONE
      | SOME rest => SOME (value::rest))
End

Definition bounded_historical_dihedral_second64_def:
  bounded_historical_dihedral_second64 environment root_delta root_four_x0
      reciprocal_certificates =
    case reciprocal_certificates of
    | root_derivative::root_logarithmic::root_four_reciprocal::
        diagonal_reciprocal::u_reciprocal::special_root_reciprocal::
        b_reciprocal::u126_reciprocal::u135_reciprocal::[] =>
      (case bounded_historical_delta_second environment of
      | NONE => NONE
      | SOME (delta,delta_gradient,delta_hessian) =>
        case bounded_historical_sqrt_second
          delta delta_gradient delta_hessian root_delta
          root_derivative root_logarithmic of
        | NONE => NONE
        | SOME (_,root_gradient,root_hessian) =>
          case bounded_historical_delta_x4_second environment of
          | NONE => NONE
          | SOME (delta_x4,delta_x4_gradient,delta_x4_hessian) =>
            case bounded_historical_u126 environment of
            | NONE => NONE
            | SOME (u126,u126_gradient) =>
              case bounded_historical_u135 environment of
              | NONE => NONE
              | SOME (u135,u135_gradient) =>
                case bounded_interval64_nth environment 0 of
                | NONE => NONE
                | SOME x0 =>
                  case bounded_interval64_scale4 x0 of
                  | NONE => NONE
                  | SOME four_x0 =>
                    if ¬bounded_interval64_sqrt_certificate
                      four_x0 root_four_x0 then NONE
                    else if ¬bounded_interval64_inv_certificate
                      root_four_x0 root_four_reciprocal then NONE
                    else
                      case bounded_historical_scale2 x0 of
                      | NONE => NONE
                      | SOME twice_x0 =>
                        if ¬bounded_interval64_inv_certificate
                          twice_x0 diagonal_reciprocal then NONE
                        else
                          case bounded_interval64_mul
                            root_delta root_four_x0 of
                          | NONE => NONE
                          | SOME b =>
                            if ¬bounded_interval64_inv_certificate
                              b b_reciprocal then NONE
                            else
                              case bounded_historical_scale2
                                bounded_atan_one of
                              | NONE => NONE
                              | SOME two =>
                                case bounded_interval64_mul
                                  two root_four_reciprocal of
                                | NONE => NONE
                                | SOME two_over_root_four =>
                                  case bounded_interval64_list_scale
                                    root_four_x0 root_gradient of
                                  | NONE => NONE
                                  | SOME b_gradient_base =>
                                    case bounded_interval64_mul
                                      root_delta two_over_root_four of
                                    | NONE => NONE
                                    | SOME b_correction =>
                                      case bounded_interval64_list_add_at
                                        b_correction 0 b_gradient_base of
                                      | NONE => NONE
                                      | SOME b_gradient =>
                                        case bounded_interval64_list_scale
                                          root_four_x0 root_hessian of
                                        | NONE => NONE
                                        | SOME b_hessian_base =>
                                          case bounded_historical_b_hessian
                                            root_delta two_over_root_four
                                            diagonal_reciprocal root_gradient
                                            b_hessian_base of
                                          | NONE => NONE
                                          | SOME b_hessian =>
                                            case bounded_historical_c_vector
                                              delta_x4 b delta_x4_gradient
                                              b_gradient of
                                            | NONE => NONE
                                            | SOME c =>
                                              case bounded_interval64_mul
                                                u126 u135 of
                                              | NONE => NONE
                                              | SOME u_product =>
                                                if
                                                  ¬bounded_interval64_inv_certificate
                                                    u_product u_reciprocal
                                                then NONE
                                                else if
                                                  ¬bounded_interval64_inv_certificate
                                                    u126 u126_reciprocal
                                                then NONE
                                                else if
                                                  ¬bounded_interval64_inv_certificate
                                                    u135 u135_reciprocal
                                                then NONE
                                                else
                                                  case
                                                    bounded_interval64_list_scale
                                                      u_reciprocal c of
                                                  | NONE => NONE
                                                  | SOME gradient_base =>
                                                    case
                                                      bounded_historical_scale2
                                                        root_delta of
                                                    | NONE => NONE
                                                    | SOME twice_root_delta =>
                                                      if
                                                        ¬bounded_interval64_inv_certificate
                                                          twice_root_delta
                                                          special_root_reciprocal
                                                      then NONE
                                                      else
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
                                                              bounded_interval64_list_scale
                                                                u126_reciprocal
                                                                u126_gradient of
                                                            | NONE => NONE
                                                            | SOME logarithmic_126 =>
                                                              case
                                                                bounded_interval64_list_scale
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
                                                                    bounded_historical_second_hessian
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
                                                                              (value,gradient,hessian))
    | _ => NONE
End

Theorem bounded_historical_point_lower_valid:
  bounded_interval64_valid value ⇒
  bounded_interval64_valid (bounded_historical_point_lower value)
Proof
  Cases_on `value`
  >> simp [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_historical_point_upper_valid:
  bounded_interval64_valid value ⇒
  bounded_interval64_valid (bounded_historical_point_upper value)
Proof
  Cases_on `value`
  >> simp [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def,
           compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_historical_point_lower_subinterval:
  bounded_interval64_valid value ⇒
  bounded_interval64_subinterval
    (bounded_historical_point_lower value) value
Proof
  Cases_on `value`
  >> simp [bounded_interval64_subinterval_def,
           compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_historical_point_upper_subinterval:
  bounded_interval64_valid value ⇒
  bounded_interval64_subinterval
    (bounded_historical_point_upper value) value
Proof
  Cases_on `value`
  >> simp [bounded_interval64_subinterval_def,
           compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def,
           compute_boundedIntervalTheory.bounded_interval64_valid_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def,
           compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_historical_monotone_coordinate_valid:
  bounded_interval64_valid value ⇒
  bounded_interval64_valid
    (bounded_historical_monotone_coordinate value derivative upper)
Proof
  rw [bounded_historical_monotone_coordinate_def]
  >> every_case_tac
  >> simp [bounded_historical_point_lower_valid,
           bounded_historical_point_upper_valid]
QED

Theorem bounded_historical_monotone_coordinate_subinterval:
  bounded_interval64_valid value ⇒
  bounded_interval64_subinterval
    (bounded_historical_monotone_coordinate value derivative upper) value
Proof
  rw [bounded_historical_monotone_coordinate_def]
  >> every_case_tac
  >> simp [bounded_interval64_subinterval_def,
           bounded_historical_point_lower_subinterval,
           bounded_historical_point_upper_subinterval]
QED

Theorem bounded_historical_monotone_environment_shape:
  ∀values derivatives upper result.
    bounded_historical_monotone_environment
      values derivatives upper = SOME result ⇒
    LENGTH result = LENGTH values ∧ LENGTH values = LENGTH derivatives
Proof
  Induct
  >> Cases_on `derivatives`
  >> rw [bounded_historical_monotone_environment_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> simp []
QED

Theorem bounded_historical_monotone_environment_valid:
  ∀values derivatives upper result.
    EVERY bounded_interval64_valid values ∧
    bounded_historical_monotone_environment
      values derivatives upper = SOME result ⇒
    EVERY bounded_interval64_valid result
Proof
  Induct
  >> Cases_on `derivatives`
  >> rw [bounded_historical_monotone_environment_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> simp [bounded_historical_monotone_coordinate_valid]
QED

Theorem bounded_historical_monotone_environment_subintervals:
  ∀values derivatives upper result.
    EVERY bounded_interval64_valid values ∧
    bounded_historical_monotone_environment
      values derivatives upper = SOME result ⇒
    LIST_REL bounded_interval64_subinterval result values
Proof
  Induct
  >> Cases_on `derivatives`
  >> rw [bounded_historical_monotone_environment_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> simp [bounded_historical_monotone_coordinate_subinterval]
QED

Theorem bounded_historical_monotone_exact_selected_contains:
  bounded_interval64_contains_int value original ⇒
  bounded_interval64_contains_int
    (bounded_historical_monotone_coordinate value derivative upper)
    (bounded_historical_monotone_exact value derivative upper original)
Proof
  Cases_on `value`
  >> rw [bounded_historical_monotone_coordinate_def,
         bounded_historical_monotone_exact_def]
  >> every_case_tac
  >> simp [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_lower_def,
           compute_boundedHistoricalDihedralFirstTheory.bounded_historical_point_upper_def,
           compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def]
QED

Theorem bounded_historical_monotone_exact_original_contains:
  bounded_interval64_valid value ∧
  bounded_interval64_contains_int value original ⇒
  bounded_interval64_contains_int value
    (bounded_historical_monotone_exact value derivative upper original)
Proof
  Cases_on `value`
  >> rw [bounded_historical_monotone_exact_def]
  >> every_case_tac
  >> fs [compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
QED

Theorem bounded_historical_monotone_exact_direction:
  bounded_interval64_valid value ∧
  bounded_interval64_contains_int value original ∧
  bounded_interval64_contains_int derivative derivative_exact ⇒
  0 ≤
    (if upper then
       (bounded_historical_monotone_exact
          value derivative upper original - original) * derivative_exact
     else
       (original - bounded_historical_monotone_exact
          value derivative upper original) * derivative_exact)
Proof
  Cases_on `value`
  >> Cases_on `derivative`
  >> rw [bounded_historical_monotone_exact_def]
  >> every_case_tac
  >> fs [compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def,
         compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
         compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> irule compute_boundedIntervalTheory.bounded_int_mul_nonnegative_same_sign
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_monotone_exact_direction_scaled40:
  bounded_interval64_valid value ∧
  bounded_interval64_contains_int value original ∧
  bounded_interval64_contains_scaled_int derivative
    (&1099511627776:int) derivative_exact ⇒
  0 ≤
    (if upper then
       (bounded_historical_monotone_exact
          value derivative upper original - original) * derivative_exact
     else
       (original - bounded_historical_monotone_exact
          value derivative upper original) * derivative_exact)
Proof
  Cases_on `value`
  >> Cases_on `derivative`
  >> rw [bounded_historical_monotone_exact_def]
  >> every_case_tac
  >> fs [compute_boundedIntervalTheory.bounded_interval64_valid_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
         compute_boundedIntervalTheory.bounded_interval64_lower_def,
         compute_boundedIntervalTheory.bounded_interval64_upper_def,
         compute_boundedIntervalTheory.bounded_signed64_nonnegative_correct,
         compute_boundedIntervalTheory.bounded_signed64_nonpositive_correct,
         compute_boundedSignedEndpointTheory.bounded_signed64_le_correct]
  >> irule compute_boundedIntervalTheory.bounded_int_mul_nonnegative_same_sign
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_secant_direction:
  2 * (selected_gradient - original_gradient) =
      (selected - original) *
        (original_derivative + selected_derivative) ∧
  0 ≤
    (if upper then
       (selected - original) * original_derivative
     else (original - selected) * original_derivative) ∧
  0 ≤
    (if upper then
       (selected - original) * selected_derivative
     else (original - selected) * selected_derivative) ⇒
  if upper then original_gradient ≤ selected_gradient
  else selected_gradient ≤ original_gradient
Proof
  strip_tac
  >> `(selected - original) *
        (original_derivative + selected_derivative) =
      (selected - original) * original_derivative +
      (selected - original) * selected_derivative` by INT_RING_TAC
  >> Cases_on `upper`
  >> fs []
  >- intLib.ARITH_TAC
  >> `(original - selected) * original_derivative =
      -((selected - original) * original_derivative)` by INT_RING_TAC
  >> `(original - selected) * selected_derivative =
      -((selected - original) * selected_derivative)` by INT_RING_TAC
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_monotone_exact_secant:
  bounded_interval64_valid value ∧
  bounded_interval64_contains_int value original ∧
  bounded_interval64_contains_int derivative original_derivative ∧
  bounded_interval64_contains_int derivative selected_derivative ∧
  selected =
    bounded_historical_monotone_exact value derivative upper original ∧
  2 * (selected_gradient - original_gradient) =
    (selected - original) *
      (original_derivative + selected_derivative) ⇒
  if upper then original_gradient ≤ selected_gradient
  else selected_gradient ≤ original_gradient
Proof
  strip_tac
  >> irule bounded_historical_secant_direction
  >> qexists_tac `original`
  >> qexists_tac `original_derivative`
  >> qexists_tac `selected`
  >> qexists_tac `selected_derivative`
  >> simp []
  >> conj_tac
  >- metis_tac [bounded_historical_monotone_exact_direction]
  >> metis_tac [bounded_historical_monotone_exact_direction]
QED

Theorem bounded_historical_monotone_exact_secant_scaled40:
  bounded_interval64_valid value ∧
  bounded_interval64_contains_int value original ∧
  bounded_interval64_contains_scaled_int derivative
    (&1099511627776:int) original_derivative ∧
  bounded_interval64_contains_scaled_int derivative
    (&1099511627776:int) selected_derivative ∧
  selected =
    bounded_historical_monotone_exact value derivative upper original ∧
  2 * (selected_gradient - original_gradient) =
    (selected - original) *
      (original_derivative + selected_derivative) ⇒
  if upper then original_gradient ≤ selected_gradient
  else selected_gradient ≤ original_gradient
Proof
  strip_tac
  >> irule bounded_historical_secant_direction
  >> qexists_tac `original`
  >> qexists_tac `original_derivative`
  >> qexists_tac `selected`
  >> qexists_tac `selected_derivative`
  >> simp []
  >> conj_tac
  >- metis_tac [bounded_historical_monotone_exact_direction_scaled40]
  >> metis_tac [bounded_historical_monotone_exact_direction_scaled40]
QED

Theorem bounded_historical_monotone_exact_environment_selected_contains:
  ∀values derivatives originals upper result.
    LIST_REL bounded_interval64_contains_int values originals ∧
    bounded_historical_monotone_environment
      values derivatives upper = SOME result ⇒
    LIST_REL bounded_interval64_contains_int result
      (bounded_historical_monotone_exact_environment
        values derivatives upper originals)
Proof
  Induct
  >> Cases_on `derivatives`
  >> Cases_on `originals`
  >> rw [bounded_historical_monotone_environment_def,
         bounded_historical_monotone_exact_environment_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> simp [bounded_historical_monotone_exact_selected_contains]
QED

Theorem bounded_historical_monotone_exact_environment_original_contains:
  ∀values derivatives originals upper result.
    EVERY bounded_interval64_valid values ∧
    LIST_REL bounded_interval64_contains_int values originals ∧
    bounded_historical_monotone_environment
      values derivatives upper = SOME result ⇒
    LIST_REL bounded_interval64_contains_int values
      (bounded_historical_monotone_exact_environment
        values derivatives upper originals)
Proof
  Induct
  >> Cases_on `derivatives`
  >> Cases_on `originals`
  >> rw [bounded_historical_monotone_environment_def,
         bounded_historical_monotone_exact_environment_def, LIST_REL_def]
  >> every_case_tac
  >> gvs [LIST_REL_def]
  >> res_tac
  >> simp [bounded_historical_monotone_exact_original_contains]
QED

Theorem bounded_historical_extreme_interval_contains_scaled_int:
  bounded_interval64_contains_scaled_int lower_value scale lower_exact ∧
  bounded_interval64_contains_scaled_int upper_value scale upper_exact ∧
  lower_exact ≤ exact_value ∧ exact_value ≤ upper_exact ⇒
  bounded_interval64_contains_scaled_int
    (bounded_historical_extreme_interval lower_value upper_value)
    scale exact_value
Proof
  Cases_on `lower_value`
  >> Cases_on `upper_value`
  >> simp [bounded_historical_extreme_interval_def,
           compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def,
           compute_boundedIntervalTheory.bounded_interval64_lower_def,
           compute_boundedIntervalTheory.bounded_interval64_upper_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_delta_x4_value_block_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_x4_value_block
    [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_x4_exact_value v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_neg_contains_int
  >> fs [bounded_historical_delta_x4_value_block_def]
  >> Cases_on
       `bounded_interval64_sum
          [bounded_interval64_neg x0;x1;x2;
           bounded_interval64_neg x3;x4;x5]`
  >> gvs []
  >> rename1
       `bounded_interval64_sum
          [bounded_interval64_neg x0;x1;x2;
           bounded_interval64_neg x3;x4;x5] = SOME linear`
  >> imp_res_tac
       compute_boundedDeltaTaylorTheory.bounded_interval64_sum6_contains_int_from_result
  >> mp_tac
       (Q.INST
         [`products` |->
            `[(bounded_interval64_neg x1,x2);
              (bounded_interval64_neg x0,x3);
              (x1,x4);(x2,x5);
              (bounded_interval64_neg x4,x5);
              (x0,linear)]`,
          `exact_values` |->
            `[(-v1)*v2;(-v0)*v3;v1*v4;v2*v5;(-v4)*v5;
              v0*((-v0)+v1+v2+(-v3)+v4+v5)]`,
          `result` |-> `result`]
         compute_boundedTaylorMulTheory.bounded_interval64_fused_products_contains_scaled_int)
  >> impl_tac
  >- (simp [LIST_REL_def,
            compute_boundedTaylorMulTheory.bounded_fused_product_input_represents_from_contains])
  >> simp [bounded_historical_delta_x4_exact_value_def]
QED

Theorem bounded_historical_delta_gradient_component_zero_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component
    0 [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value 0 v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_neg_contains_int
  >> fs [bounded_historical_delta_gradient_component_def]
  >> mp_tac
       (Q.INST
          [`products` |->
             `[(bounded_interval64_neg x0,x3);
               (bounded_interval64_neg x0,x3);
               (x1,x3);(x1,x4);(bounded_interval64_neg x1,x5);
               (x2,x3);(bounded_interval64_neg x2,x4);(x2,x5);
               (bounded_interval64_neg x3,x3);(x3,x4);(x3,x5)]`,
           `exact_values` |->
             `[(-v0)*v3;(-v0)*v3;v1*v3;v1*v4;(-v1)*v5;
               v2*v3;(-v2)*v4;v2*v5;(-v3)*v3;v3*v4;v3*v5]`,
           `result` |-> `result`]
          compute_boundedTaylorMulTheory.bounded_interval64_fused_products_contains_scaled_int)
  >> impl_tac
  >- (simp [LIST_REL_def,
            compute_boundedTaylorMulTheory.bounded_fused_product_input_represents_from_contains])
  >> simp [bounded_historical_delta_gradient_value_def]
QED

fun prove_historical_delta_gradient_component products exact_values =
  strip_tac
  >> imp_res_tac
       compute_boundedIntervalAddTheory.bounded_interval64_neg_contains_int
  >> fs [bounded_historical_delta_gradient_component_def]
  >> mp_tac
       (INST
          [``products:(bounded_interval64 # bounded_interval64) list`` |->
             products,
           ``exact_values:int list`` |-> exact_values,
           ``result:bounded_interval64`` |-> ``result:bounded_interval64``]
          compute_boundedTaylorMulTheory.bounded_interval64_fused_products_contains_scaled_int)
  >> impl_tac
  >- (simp [LIST_REL_def,
            compute_boundedTaylorMulTheory.bounded_fused_product_input_represents_from_contains])
  >> simp [bounded_historical_delta_gradient_value_def];

Theorem bounded_historical_delta_gradient_component_one_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component
    1 [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value 1 v0 v1 v2 v3 v4 v5)
Proof
  prove_historical_delta_gradient_component
    ``[(x0,x3);(x0,x4);(bounded_interval64_neg x0,x5);
       (bounded_interval64_neg x1,x4);
       (bounded_interval64_neg x1,x4);
       (bounded_interval64_neg x2,x3);(x2,x4);(x2,x5);
       (x3,x4);(bounded_interval64_neg x4,x4);(x4,x5)]``
    ``[v0*v3;v0*v4;(-v0)*v5;(-v1)*v4;(-v1)*v4;
       (-v2)*v3;v2*v4;v2*v5;v3*v4;(-v4)*v4;v4*v5]``
QED

Theorem bounded_historical_delta_gradient_component_two_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component
    2 [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value 2 v0 v1 v2 v3 v4 v5)
Proof
  prove_historical_delta_gradient_component
    ``[(x0,x3);(bounded_interval64_neg x0,x4);(x0,x5);
       (bounded_interval64_neg x1,x3);(x1,x4);(x1,x5);
       (bounded_interval64_neg x2,x5);
       (bounded_interval64_neg x2,x5);
       (x3,x5);(x4,x5);(bounded_interval64_neg x5,x5)]``
    ``[v0*v3;(-v0)*v4;v0*v5;(-v1)*v3;v1*v4;v1*v5;
       (-v2)*v5;(-v2)*v5;v3*v5;v4*v5;(-v5)*v5]``
QED

Theorem bounded_historical_delta_gradient_component_three_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component
    3 [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value 3 v0 v1 v2 v3 v4 v5)
Proof
  prove_historical_delta_gradient_component
    ``[(bounded_interval64_neg x0,x0);(x0,x1);(x0,x2);
       (bounded_interval64_neg x0,x3);
       (bounded_interval64_neg x0,x3);
       (x0,x4);(x0,x5);(bounded_interval64_neg x1,x2);
       (x1,x4);(x2,x5);(bounded_interval64_neg x4,x5)]``
    ``[(-v0)*v0;v0*v1;v0*v2;(-v0)*v3;(-v0)*v3;
       v0*v4;v0*v5;(-v1)*v2;v1*v4;v2*v5;(-v4)*v5]``
QED

Theorem bounded_historical_delta_gradient_component_four_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component
    4 [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value 4 v0 v1 v2 v3 v4 v5)
Proof
  prove_historical_delta_gradient_component
    ``[(x0,x1);(bounded_interval64_neg x0,x2);(x0,x3);
       (bounded_interval64_neg x1,x1);(x1,x2);(x1,x3);
       (bounded_interval64_neg x1,x4);
       (bounded_interval64_neg x1,x4);
       (x1,x5);(x2,x5);(bounded_interval64_neg x3,x5)]``
    ``[v0*v1;(-v0)*v2;v0*v3;(-v1)*v1;v1*v2;v1*v3;
       (-v1)*v4;(-v1)*v4;v1*v5;v2*v5;(-v3)*v5]``
QED

Theorem bounded_historical_delta_gradient_component_five_contains_scaled_int:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component
    5 [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value 5 v0 v1 v2 v3 v4 v5)
Proof
  prove_historical_delta_gradient_component
    ``[(bounded_interval64_neg x0,x1);(x0,x2);(x0,x3);
       (x1,x2);(x1,x4);(bounded_interval64_neg x2,x2);
       (x2,x3);(x2,x4);
       (bounded_interval64_neg x2,x5);
       (bounded_interval64_neg x2,x5);
       (bounded_interval64_neg x3,x4)]``
    ``[(-v0)*v1;v0*v2;v0*v3;v1*v2;v1*v4;(-v2)*v2;
       v2*v3;v2*v4;(-v2)*v5;(-v2)*v5;(-v3)*v4]``
QED

Theorem bounded_historical_delta_gradient_component_contains_scaled_int:
  coordinate < 6 ∧
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_historical_delta_gradient_component coordinate
    [x0;x1;x2;x3;x4;x5] = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >>
  `coordinate = 0 ∨ coordinate = 1 ∨ coordinate = 2 ∨
   coordinate = 3 ∨ coordinate = 4 ∨ coordinate = 5` by DECIDE_TAC
  >> metis_tac
       [bounded_historical_delta_gradient_component_zero_contains_scaled_int,
        bounded_historical_delta_gradient_component_one_contains_scaled_int,
        bounded_historical_delta_gradient_component_two_contains_scaled_int,
        bounded_historical_delta_gradient_component_three_contains_scaled_int,
        bounded_historical_delta_gradient_component_four_contains_scaled_int,
        bounded_historical_delta_gradient_component_five_contains_scaled_int]
QED

Theorem bounded_historical_delta_gradient_value_characterizations:
  bounded_delta_value (v0 + h) v1 v2 v3 v4 v5 -
      bounded_delta_value (v0 - h) v1 v2 v3 v4 v5 =
    2 * h * bounded_historical_delta_gradient_value
      0 v0 v1 v2 v3 v4 v5 ∧
  bounded_delta_value v0 (v1 + h) v2 v3 v4 v5 -
      bounded_delta_value v0 (v1 - h) v2 v3 v4 v5 =
    2 * h * bounded_historical_delta_gradient_value
      1 v0 v1 v2 v3 v4 v5 ∧
  bounded_delta_value v0 v1 (v2 + h) v3 v4 v5 -
      bounded_delta_value v0 v1 (v2 - h) v3 v4 v5 =
    2 * h * bounded_historical_delta_gradient_value
      2 v0 v1 v2 v3 v4 v5 ∧
  bounded_delta_value v0 v1 v2 (v3 + h) v4 v5 -
      bounded_delta_value v0 v1 v2 (v3 - h) v4 v5 =
    2 * h * bounded_historical_delta_gradient_value
      3 v0 v1 v2 v3 v4 v5 ∧
  bounded_delta_value v0 v1 v2 v3 (v4 + h) v5 -
      bounded_delta_value v0 v1 v2 v3 (v4 - h) v5 =
    2 * h * bounded_historical_delta_gradient_value
      4 v0 v1 v2 v3 v4 v5 ∧
  bounded_delta_value v0 v1 v2 v3 v4 (v5 + h) -
      bounded_delta_value v0 v1 v2 v3 v4 (v5 - h) =
    2 * h * bounded_historical_delta_gradient_value
      5 v0 v1 v2 v3 v4 v5
Proof
  simp [bounded_historical_delta_gradient_value_def,
        compute_boundedDeltaSpecializationTheory.bounded_delta_value_def]
  >> rpt conj_tac
  >> INT_RING_TAC
QED

Theorem bounded_historical_delta_coordinate_differences:
  2 * (bounded_delta_value replacement v1 v2 v3 v4 v5 -
    bounded_delta_value v0 v1 v2 v3 v4 v5) =
    (replacement - v0) *
      (bounded_historical_delta_gradient_value 0 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_gradient_value
         0 replacement v1 v2 v3 v4 v5) ∧
  2 * (bounded_delta_value v0 replacement v2 v3 v4 v5 -
    bounded_delta_value v0 v1 v2 v3 v4 v5) =
    (replacement - v1) *
      (bounded_historical_delta_gradient_value 1 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_gradient_value
         1 v0 replacement v2 v3 v4 v5) ∧
  2 * (bounded_delta_value v0 v1 replacement v3 v4 v5 -
    bounded_delta_value v0 v1 v2 v3 v4 v5) =
    (replacement - v2) *
      (bounded_historical_delta_gradient_value 2 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_gradient_value
         2 v0 v1 replacement v3 v4 v5) ∧
  2 * (bounded_delta_value v0 v1 v2 replacement v4 v5 -
    bounded_delta_value v0 v1 v2 v3 v4 v5) =
    (replacement - v3) *
      (bounded_historical_delta_gradient_value 3 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_gradient_value
         3 v0 v1 v2 replacement v4 v5) ∧
  2 * (bounded_delta_value v0 v1 v2 v3 replacement v5 -
    bounded_delta_value v0 v1 v2 v3 v4 v5) =
    (replacement - v4) *
      (bounded_historical_delta_gradient_value 4 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_gradient_value
         4 v0 v1 v2 v3 replacement v5) ∧
  2 * (bounded_delta_value v0 v1 v2 v3 v4 replacement -
    bounded_delta_value v0 v1 v2 v3 v4 v5) =
    (replacement - v5) *
      (bounded_historical_delta_gradient_value 5 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_gradient_value
         5 v0 v1 v2 v3 v4 replacement)
Proof
  simp [bounded_historical_delta_gradient_value_def,
        compute_boundedDeltaSpecializationTheory.bounded_delta_value_def]
  >> rpt conj_tac
  >> INT_RING_TAC
QED

Theorem bounded_historical_delta_coordinate_step_zero_from_endpoints:
  selected = bounded_historical_monotone_exact x0 g0 upper v0 ∧
  bounded_interval64_valid x0 ∧
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_scaled_int g0 (&1099511627776:int)
    (bounded_historical_delta_gradient_value 0 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_scaled_int g0 (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      0 selected v1 v2 v3 v4 v5) ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value selected v1 v2 v3 v4 v5
  else
    bounded_delta_value selected v1 v2 v3 v4 v5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_delta_value selected v1 v2 v3 v4 v5 -
         bounded_delta_value v0 v1 v2 v3 v4 v5) =
      (selected - v0) *
        (bounded_historical_delta_gradient_value 0 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_gradient_value
           0 selected v1 v2 v3 v4 v5)` by
       metis_tac [bounded_historical_delta_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant_scaled40
  >> qexists_tac `g0`
  >> qexists_tac `v0`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 0 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 0 selected v1 v2 v3 v4 v5`
  >> qexists_tac `x0`
  >> metis_tac []
QED

Theorem bounded_historical_delta_coordinate_step_one_from_endpoints:
  selected = bounded_historical_monotone_exact x1 g1 upper v1 ∧
  bounded_interval64_valid x1 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_scaled_int g1 (&1099511627776:int)
    (bounded_historical_delta_gradient_value 1 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_scaled_int g1 (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      1 v0 selected v2 v3 v4 v5) ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value v0 selected v2 v3 v4 v5
  else
    bounded_delta_value v0 selected v2 v3 v4 v5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> irule bounded_historical_monotone_exact_secant_scaled40
  >> qexists_tac `g1`
  >> qexists_tac `v1`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 1 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 1 v0 selected v2 v3 v4 v5`
  >> qexists_tac `x1`
  >> metis_tac [bounded_historical_delta_coordinate_differences]
QED

Theorem bounded_historical_delta_coordinate_step_two_from_endpoints:
  selected = bounded_historical_monotone_exact x2 g2 upper v2 ∧
  bounded_interval64_valid x2 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_scaled_int g2 (&1099511627776:int)
    (bounded_historical_delta_gradient_value 2 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_scaled_int g2 (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      2 v0 v1 selected v3 v4 v5) ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value v0 v1 selected v3 v4 v5
  else
    bounded_delta_value v0 v1 selected v3 v4 v5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> irule bounded_historical_monotone_exact_secant_scaled40
  >> qexists_tac `g2`
  >> qexists_tac `v2`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 2 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 2 v0 v1 selected v3 v4 v5`
  >> qexists_tac `x2`
  >> metis_tac [bounded_historical_delta_coordinate_differences]
QED

Theorem bounded_historical_delta_coordinate_step_three_from_endpoints:
  selected = bounded_historical_monotone_exact x3 g3 upper v3 ∧
  bounded_interval64_valid x3 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_scaled_int g3 (&1099511627776:int)
    (bounded_historical_delta_gradient_value 3 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_scaled_int g3 (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      3 v0 v1 v2 selected v4 v5) ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value v0 v1 v2 selected v4 v5
  else
    bounded_delta_value v0 v1 v2 selected v4 v5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> irule bounded_historical_monotone_exact_secant_scaled40
  >> qexists_tac `g3`
  >> qexists_tac `v3`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 3 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 3 v0 v1 v2 selected v4 v5`
  >> qexists_tac `x3`
  >> metis_tac [bounded_historical_delta_coordinate_differences]
QED

Theorem bounded_historical_delta_coordinate_step_four_from_endpoints:
  selected = bounded_historical_monotone_exact x4 g4 upper v4 ∧
  bounded_interval64_valid x4 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_scaled_int g4 (&1099511627776:int)
    (bounded_historical_delta_gradient_value 4 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_scaled_int g4 (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      4 v0 v1 v2 v3 selected v5) ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value v0 v1 v2 v3 selected v5
  else
    bounded_delta_value v0 v1 v2 v3 selected v5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> irule bounded_historical_monotone_exact_secant_scaled40
  >> qexists_tac `g4`
  >> qexists_tac `v4`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 4 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 4 v0 v1 v2 v3 selected v5`
  >> qexists_tac `x4`
  >> metis_tac [bounded_historical_delta_coordinate_differences]
QED

Theorem bounded_historical_delta_coordinate_step_five_from_endpoints:
  selected = bounded_historical_monotone_exact x5 g5 upper v5 ∧
  bounded_interval64_valid x5 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_interval64_contains_scaled_int g5 (&1099511627776:int)
    (bounded_historical_delta_gradient_value 5 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_scaled_int g5 (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      5 v0 v1 v2 v3 v4 selected) ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 selected
  else
    bounded_delta_value v0 v1 v2 v3 v4 selected ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> irule bounded_historical_monotone_exact_secant_scaled40
  >> qexists_tac `g5`
  >> qexists_tac `v5`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 5 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_gradient_value 5 v0 v1 v2 v3 v4 selected`
  >> qexists_tac `x5`
  >> metis_tac [bounded_historical_delta_coordinate_differences]
QED

Theorem bounded_historical_delta_gradient_coordinate_differences:
  coordinate < 6 ⇒
  2 * (bounded_historical_delta_gradient_value
      coordinate replacement v1 v2 v3 v4 v5 -
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5) =
    (replacement - v0) *
      (bounded_historical_delta_hessian_value
         coordinate 0 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_hessian_value
         coordinate 0 replacement v1 v2 v3 v4 v5) ∧
  2 * (bounded_historical_delta_gradient_value
      coordinate v0 replacement v2 v3 v4 v5 -
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5) =
    (replacement - v1) *
      (bounded_historical_delta_hessian_value
         coordinate 1 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_hessian_value
         coordinate 1 v0 replacement v2 v3 v4 v5) ∧
  2 * (bounded_historical_delta_gradient_value
      coordinate v0 v1 replacement v3 v4 v5 -
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5) =
    (replacement - v2) *
      (bounded_historical_delta_hessian_value
         coordinate 2 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_hessian_value
         coordinate 2 v0 v1 replacement v3 v4 v5) ∧
  2 * (bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 replacement v4 v5 -
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5) =
    (replacement - v3) *
      (bounded_historical_delta_hessian_value
         coordinate 3 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_hessian_value
         coordinate 3 v0 v1 v2 replacement v4 v5) ∧
  2 * (bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 replacement v5 -
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5) =
    (replacement - v4) *
      (bounded_historical_delta_hessian_value
         coordinate 4 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_hessian_value
         coordinate 4 v0 v1 v2 v3 replacement v5) ∧
  2 * (bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 replacement -
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5) =
    (replacement - v5) *
      (bounded_historical_delta_hessian_value
         coordinate 5 v0 v1 v2 v3 v4 v5 +
       bounded_historical_delta_hessian_value
         coordinate 5 v0 v1 v2 v3 v4 replacement)
Proof
  strip_tac
  >> Cases_on `coordinate = 0`
  >> fs [bounded_historical_delta_gradient_value_def,
         bounded_historical_delta_hessian_value_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >- (rpt conj_tac >> INT_RING_TAC)
  >> Cases_on `coordinate = 1`
  >> fs [bounded_historical_delta_gradient_value_def,
         bounded_historical_delta_hessian_value_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >- (rpt conj_tac >> INT_RING_TAC)
  >> Cases_on `coordinate = 2`
  >> fs [bounded_historical_delta_gradient_value_def,
         bounded_historical_delta_hessian_value_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >- (rpt conj_tac >> INT_RING_TAC)
  >> Cases_on `coordinate = 3`
  >> fs [bounded_historical_delta_gradient_value_def,
         bounded_historical_delta_hessian_value_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >- (rpt conj_tac >> INT_RING_TAC)
  >> Cases_on `coordinate = 4`
  >> fs [bounded_historical_delta_gradient_value_def,
         bounded_historical_delta_hessian_value_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >- (rpt conj_tac >> INT_RING_TAC)
  >> `coordinate = 5` by DECIDE_TAC
  >> fs [bounded_historical_delta_gradient_value_def,
         bounded_historical_delta_hessian_value_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> rpt conj_tac
  >> INT_RING_TAC
QED

Theorem bounded_historical_delta_hessian_rows_contains_ints:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
  bounded_hessian64_rows hessian = SOME rows ⇒
  LIST_REL (LIST_REL bounded_interval64_contains_int) rows
    (bounded_delta_hessian_value_matrix v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> `LIST_REL bounded_interval64_contains_int hessian
        (bounded_delta_hessian_values v0 v1 v2 v3 v4 v5)` by
       metis_tac
         [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_contains_ints]
  >> metis_tac
       [compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_rows,
        compute_boundedTaylorGradientTheory.bounded_hessian64_rows_list_rel]
QED

Theorem bounded_historical_delta_hessian_row_entry_contains_int:
  coordinate < 6 ∧ column < 6 ∧
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
  bounded_hessian64_rows hessian = SOME rows ⇒
  bounded_interval64_contains_int (EL column (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate column v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> `LIST_REL (LIST_REL bounded_interval64_contains_int) rows
        (bounded_delta_hessian_value_matrix v0 v1 v2 v3 v4 v5)` by
       metis_tac [bounded_historical_delta_hessian_rows_contains_ints]
  >> `LENGTH
        (bounded_delta_hessian_value_matrix v0 v1 v2 v3 v4 v5) = 6 ∧
      EVERY ($= 6 o LENGTH)
        (bounded_delta_hessian_value_matrix v0 v1 v2 v3 v4 v5)` by
       simp [compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_matrix_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_values_def,
         compute_boundedDeltaTaylorTheory.bounded_delta_hessian_value_rows_def,
         compute_boundedTaylorGradientTheory.bounded_hessian64_rows_def]
  >> fs [LIST_REL_EL_EQN, EVERY_EL,
         bounded_historical_delta_hessian_value_def]
QED

Theorem bounded_historical_delta_gradient_coordinate_step_zero_from_endpoints:
  coordinate < 6 ∧
  selected = bounded_historical_monotone_exact x0
    (EL 0 (EL coordinate rows)) upper v0 ∧
  bounded_interval64_valid x0 ∧
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int (EL 0 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 0 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 0 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 0 selected v1 v2 v3 v4 v5) ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value
      coordinate selected v1 v2 v3 v4 v5
  else
    bounded_historical_delta_gradient_value
      coordinate selected v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_historical_delta_gradient_value
            coordinate selected v1 v2 v3 v4 v5 -
         bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5) =
      (selected - v0) *
        (bounded_historical_delta_hessian_value
            coordinate 0 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_hessian_value
            coordinate 0 selected v1 v2 v3 v4 v5)` by
       metis_tac [bounded_historical_delta_gradient_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant
  >> qexists_tac `EL 0 (EL coordinate rows)`
  >> qexists_tac `v0`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 0 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 0 selected v1 v2 v3 v4 v5`
  >> qexists_tac `x0`
  >> metis_tac []
QED

Theorem bounded_historical_delta_gradient_coordinate_step_one_from_endpoints:
  coordinate < 6 ∧
  selected = bounded_historical_monotone_exact x1
    (EL 1 (EL coordinate rows)) upper v1 ∧
  bounded_interval64_valid x1 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int (EL 1 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 1 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 1 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 1 v0 selected v2 v3 v4 v5) ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value
      coordinate v0 selected v2 v3 v4 v5
  else
    bounded_historical_delta_gradient_value
      coordinate v0 selected v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_historical_delta_gradient_value
            coordinate v0 selected v2 v3 v4 v5 -
         bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5) =
      (selected - v1) *
        (bounded_historical_delta_hessian_value
            coordinate 1 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_hessian_value
            coordinate 1 v0 selected v2 v3 v4 v5)` by
       metis_tac [bounded_historical_delta_gradient_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant
  >> qexists_tac `EL 1 (EL coordinate rows)`
  >> qexists_tac `v1`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 1 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 1 v0 selected v2 v3 v4 v5`
  >> qexists_tac `x1`
  >> metis_tac []
QED

Theorem bounded_historical_delta_gradient_coordinate_step_two_from_endpoints:
  coordinate < 6 ∧
  selected = bounded_historical_monotone_exact x2
    (EL 2 (EL coordinate rows)) upper v2 ∧
  bounded_interval64_valid x2 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int (EL 2 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 2 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 2 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 2 v0 v1 selected v3 v4 v5) ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value
      coordinate v0 v1 selected v3 v4 v5
  else
    bounded_historical_delta_gradient_value
      coordinate v0 v1 selected v3 v4 v5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_historical_delta_gradient_value
            coordinate v0 v1 selected v3 v4 v5 -
         bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5) =
      (selected - v2) *
        (bounded_historical_delta_hessian_value
            coordinate 2 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_hessian_value
            coordinate 2 v0 v1 selected v3 v4 v5)` by
       metis_tac [bounded_historical_delta_gradient_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant
  >> qexists_tac `EL 2 (EL coordinate rows)`
  >> qexists_tac `v2`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 2 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 2 v0 v1 selected v3 v4 v5`
  >> qexists_tac `x2`
  >> metis_tac []
QED

Theorem bounded_historical_delta_gradient_coordinate_step_three_from_endpoints:
  coordinate < 6 ∧
  selected = bounded_historical_monotone_exact x3
    (EL 3 (EL coordinate rows)) upper v3 ∧
  bounded_interval64_valid x3 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int (EL 3 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 3 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 3 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 3 v0 v1 v2 selected v4 v5) ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 selected v4 v5
  else
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 selected v4 v5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 selected v4 v5 -
         bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5) =
      (selected - v3) *
        (bounded_historical_delta_hessian_value
            coordinate 3 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_hessian_value
            coordinate 3 v0 v1 v2 selected v4 v5)` by
       metis_tac [bounded_historical_delta_gradient_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant
  >> qexists_tac `EL 3 (EL coordinate rows)`
  >> qexists_tac `v3`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 3 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 3 v0 v1 v2 selected v4 v5`
  >> qexists_tac `x3`
  >> metis_tac []
QED

Theorem bounded_historical_delta_gradient_coordinate_step_four_from_endpoints:
  coordinate < 6 ∧
  selected = bounded_historical_monotone_exact x4
    (EL 4 (EL coordinate rows)) upper v4 ∧
  bounded_interval64_valid x4 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int (EL 4 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 4 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 4 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 4 v0 v1 v2 v3 selected v5) ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 selected v5
  else
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 selected v5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 selected v5 -
         bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5) =
      (selected - v4) *
        (bounded_historical_delta_hessian_value
            coordinate 4 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_hessian_value
            coordinate 4 v0 v1 v2 v3 selected v5)` by
       metis_tac [bounded_historical_delta_gradient_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant
  >> qexists_tac `EL 4 (EL coordinate rows)`
  >> qexists_tac `v4`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 4 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 4 v0 v1 v2 v3 selected v5`
  >> qexists_tac `x4`
  >> metis_tac []
QED

Theorem bounded_historical_delta_gradient_coordinate_step_five_from_endpoints:
  coordinate < 6 ∧
  selected = bounded_historical_monotone_exact x5
    (EL 5 (EL coordinate rows)) upper v5 ∧
  bounded_interval64_valid x5 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_interval64_contains_int (EL 5 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 5 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 5 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 5 v0 v1 v2 v3 v4 selected) ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 selected
  else
    bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 selected ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  strip_tac
  >> `2 *
        (bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 selected -
         bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5) =
      (selected - v5) *
        (bounded_historical_delta_hessian_value
            coordinate 5 v0 v1 v2 v3 v4 v5 +
         bounded_historical_delta_hessian_value
            coordinate 5 v0 v1 v2 v3 v4 selected)` by
       metis_tac [bounded_historical_delta_gradient_coordinate_differences]
  >> irule bounded_historical_monotone_exact_secant
  >> qexists_tac `EL 5 (EL coordinate rows)`
  >> qexists_tac `v5`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 5 v0 v1 v2 v3 v4 v5`
  >> qexists_tac `selected`
  >> qexists_tac
       `bounded_historical_delta_hessian_value
          coordinate 5 v0 v1 v2 v3 v4 selected`
  >> qexists_tac `x5`
  >> metis_tac []
QED

Definition bounded_historical_delta_gradient_path_endpoint_contract_def:
  bounded_historical_delta_gradient_path_endpoint_contract coordinate rows
      upper [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [s0;s1;s2;s3;s4;s5] =
  (coordinate < 6 ∧
  s0 = bounded_historical_monotone_exact x0
    (EL 0 (EL coordinate rows)) upper v0 ∧
  s1 = bounded_historical_monotone_exact x1
    (EL 1 (EL coordinate rows)) upper v1 ∧
  s2 = bounded_historical_monotone_exact x2
    (EL 2 (EL coordinate rows)) upper v2 ∧
  s3 = bounded_historical_monotone_exact x3
    (EL 3 (EL coordinate rows)) upper v3 ∧
  s4 = bounded_historical_monotone_exact x4
    (EL 4 (EL coordinate rows)) upper v4 ∧
  s5 = bounded_historical_monotone_exact x5
    (EL 5 (EL coordinate rows)) upper v5 ∧
  bounded_interval64_valid x0 ∧
  bounded_interval64_valid x1 ∧
  bounded_interval64_valid x2 ∧
  bounded_interval64_valid x3 ∧
  bounded_interval64_valid x4 ∧
  bounded_interval64_valid x5 ∧
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_contains_int x1 v1 ∧
  bounded_interval64_contains_int x2 v2 ∧
  bounded_interval64_contains_int x3 v3 ∧
  bounded_interval64_contains_int x4 v4 ∧
  bounded_interval64_contains_int x5 v5 ∧
  bounded_interval64_contains_int (EL 0 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 0 v0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 0 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 0 s0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 1 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 1 s0 v1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 1 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 1 s0 s1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 2 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 2 s0 s1 v2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 2 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 2 s0 s1 s2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 3 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 3 s0 s1 s2 v3 v4 v5) ∧
  bounded_interval64_contains_int (EL 3 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 3 s0 s1 s2 s3 v4 v5) ∧
  bounded_interval64_contains_int (EL 4 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 4 s0 s1 s2 s3 v4 v5) ∧
  bounded_interval64_contains_int (EL 4 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 4 s0 s1 s2 s3 s4 v5) ∧
  bounded_interval64_contains_int (EL 5 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 5 s0 s1 s2 s3 s4 v5) ∧
  bounded_interval64_contains_int (EL 5 (EL coordinate rows))
    (bounded_historical_delta_hessian_value
      coordinate 5 s0 s1 s2 s3 s4 s5)) ∧
  bounded_historical_delta_gradient_path_endpoint_contract
    _ _ _ _ _ _ = F
End

val bounded_historical_delta_gradient_coordinate_path_from_endpoints =
Q.store_thm (
  "bounded_historical_delta_gradient_coordinate_path_from_endpoints",
  `
  bounded_historical_delta_gradient_path_endpoint_contract coordinate rows
    upper [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [s0;s1;s2;s3;s4;s5] ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value coordinate s0 s1 s2 s3 s4 s5
  else
    bounded_historical_delta_gradient_value coordinate s0 s1 s2 s3 s4 s5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5`,
  simp_tac (srw_ss())
    [bounded_historical_delta_gradient_path_endpoint_contract_def]
  >> strip_tac
  >> `if upper then
        bounded_historical_delta_gradient_value
          coordinate v0 v1 v2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 v1 v2 v3 v4 v5
      else
        bounded_historical_delta_gradient_value
          coordinate s0 v1 v2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate v0 v1 v2 v3 v4 v5` by
       metis_tac
         [bounded_historical_delta_gradient_coordinate_step_zero_from_endpoints,
          EL]
  >> `if upper then
        bounded_historical_delta_gradient_value
          coordinate s0 v1 v2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 v2 v3 v4 v5
      else
        bounded_historical_delta_gradient_value
          coordinate s0 s1 v2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 v1 v2 v3 v4 v5` by
       metis_tac
         [bounded_historical_delta_gradient_coordinate_step_one_from_endpoints,
          EL]
  >> `if upper then
        bounded_historical_delta_gradient_value
          coordinate s0 s1 v2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 v3 v4 v5
      else
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 v2 v3 v4 v5` by
       metis_tac
         [bounded_historical_delta_gradient_coordinate_step_two_from_endpoints,
          EL]
  >> `if upper then
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 v3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 v4 v5
      else
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 v3 v4 v5` by
       metis_tac
         [bounded_historical_delta_gradient_coordinate_step_three_from_endpoints,
          EL]
  >> `if upper then
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 v4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 s4 v5
      else
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 s4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 v4 v5` by
       metis_tac
         [bounded_historical_delta_gradient_coordinate_step_four_from_endpoints,
          EL]
  >> `if upper then
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 s4 v5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 s4 s5
      else
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 s4 s5 ≤
        bounded_historical_delta_gradient_value
          coordinate s0 s1 s2 s3 s4 v5` by
       metis_tac
         [bounded_historical_delta_gradient_coordinate_step_five_from_endpoints,
          EL]
  >> Cases_on `upper`
  >> fs []
  >> metis_tac [integerTheory.INT_LE_TRANS]);

Definition bounded_historical_delta_gradient_path_source_contract_def:
  bounded_historical_delta_gradient_path_source_contract coordinate rows
      upper [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [s0;s1;s2;s3;s4;s5] =
  (coordinate < 6 ∧
   s0 = bounded_historical_monotone_exact x0
     (EL 0 (EL coordinate rows)) upper v0 ∧
   s1 = bounded_historical_monotone_exact x1
     (EL 1 (EL coordinate rows)) upper v1 ∧
   s2 = bounded_historical_monotone_exact x2
     (EL 2 (EL coordinate rows)) upper v2 ∧
   s3 = bounded_historical_monotone_exact x3
     (EL 3 (EL coordinate rows)) upper v3 ∧
   s4 = bounded_historical_monotone_exact x4
     (EL 4 (EL coordinate rows)) upper v4 ∧
   s5 = bounded_historical_monotone_exact x5
     (EL 5 (EL coordinate rows)) upper v5 ∧
   EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
   LIST_REL bounded_interval64_contains_int
     [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
   ∃hessian.
     bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
     bounded_hessian64_rows hessian = SOME rows) ∧
  bounded_historical_delta_gradient_path_source_contract
    _ _ _ _ _ _ = F
End

Theorem bounded_historical_delta_gradient_path_endpoint_contract_from_source:
  bounded_historical_delta_gradient_path_source_contract coordinate rows
    upper [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [s0;s1;s2;s3;s4;s5] ⇒
  bounded_historical_delta_gradient_path_endpoint_contract coordinate rows
    upper [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [s0;s1;s2;s3;s4;s5]
Proof
  simp_tac (srw_ss())
    [bounded_historical_delta_gradient_path_source_contract_def,
     LIST_REL_def]
  >> strip_tac
  >> fs [bounded_historical_delta_gradient_path_endpoint_contract_def,
         bounded_historical_monotone_exact_original_contains]
  >> rpt conj_tac
  >> once_rewrite_tac [GSYM (CONJUNCT1 EL)]
  >> irule bounded_historical_delta_hessian_row_entry_contains_int
  >> simp []
  >> metis_tac [bounded_historical_monotone_exact_original_contains]
QED

Theorem bounded_historical_delta_gradient_coordinate_path_from_source:
  bounded_historical_delta_gradient_path_source_contract coordinate rows
    upper [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [s0;s1;s2;s3;s4;s5] ⇒
  if upper then
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5 ≤
    bounded_historical_delta_gradient_value coordinate s0 s1 s2 s3 s4 s5
  else
    bounded_historical_delta_gradient_value coordinate s0 s1 s2 s3 s4 s5 ≤
    bounded_historical_delta_gradient_value coordinate v0 v1 v2 v3 v4 v5
Proof
  metis_tac
    [bounded_historical_delta_gradient_path_endpoint_contract_from_source,
     bounded_historical_delta_gradient_coordinate_path_from_endpoints]
QED

Theorem bounded_historical_delta_gradient_box_entry_contains_scaled_int:
  coordinate < 6 ∧
  EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
  LIST_REL bounded_interval64_contains_int
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
  bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
  bounded_hessian64_rows hessian = SOME rows ∧
  bounded_historical_delta_gradient_box_entry
    [x0;x1;x2;x3;x4;x5] (EL coordinate rows) coordinate = SOME result ⇒
  bounded_interval64_contains_scaled_int result (&1099511627776:int)
    (bounded_historical_delta_gradient_value
      coordinate v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> fs [bounded_historical_delta_gradient_box_entry_def]
  >> every_case_tac
  >> fs []
  >> imp_res_tac bounded_historical_monotone_environment_shape
  >> Cases_on `EL coordinate rows`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs [bounded_historical_monotone_environment_def]
  >> gvs []
  >> irule bounded_historical_extreme_interval_contains_scaled_int
  >> conj_tac
  >-
   (qexists_tac
      `bounded_historical_delta_gradient_value coordinate
         (bounded_historical_monotone_exact x0 h F v0)
         (bounded_historical_monotone_exact x1 h' F v1)
         (bounded_historical_monotone_exact x2 h'' F v2)
         (bounded_historical_monotone_exact x3 h''' F v3)
         (bounded_historical_monotone_exact x4 h'''' F v4)
         (bounded_historical_monotone_exact x5 h''''' F v5)`
    >> conj_tac
    >-
     (`bounded_historical_delta_gradient_path_source_contract coordinate rows F
         [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
         [bounded_historical_monotone_exact x0 h F v0;
          bounded_historical_monotone_exact x1 h' F v1;
          bounded_historical_monotone_exact x2 h'' F v2;
          bounded_historical_monotone_exact x3 h''' F v3;
          bounded_historical_monotone_exact x4 h'''' F v4;
          bounded_historical_monotone_exact x5 h''''' F v5]` by
        simp [bounded_historical_delta_gradient_path_source_contract_def,
              LIST_REL_def]
      >> metis_tac
           [bounded_historical_delta_gradient_coordinate_path_from_source])
    >> irule bounded_historical_delta_gradient_component_contains_scaled_int
    >> simp []
    >> qexistsl_tac
         [`bounded_historical_monotone_coordinate x0 h F`,
          `bounded_historical_monotone_coordinate x1 h' F`,
          `bounded_historical_monotone_coordinate x2 h'' F`,
          `bounded_historical_monotone_coordinate x3 h''' F`,
          `bounded_historical_monotone_coordinate x4 h'''' F`,
          `bounded_historical_monotone_coordinate x5 h''''' F`]
    >> simp [bounded_historical_monotone_exact_selected_contains])
  >> qexists_tac
       `bounded_historical_delta_gradient_value coordinate
          (bounded_historical_monotone_exact x0 h T v0)
          (bounded_historical_monotone_exact x1 h' T v1)
          (bounded_historical_monotone_exact x2 h'' T v2)
          (bounded_historical_monotone_exact x3 h''' T v3)
          (bounded_historical_monotone_exact x4 h'''' T v4)
          (bounded_historical_monotone_exact x5 h''''' T v5)`
  >> conj_tac
  >-
   (`bounded_historical_delta_gradient_path_source_contract coordinate rows T
       [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
       [bounded_historical_monotone_exact x0 h T v0;
        bounded_historical_monotone_exact x1 h' T v1;
        bounded_historical_monotone_exact x2 h'' T v2;
        bounded_historical_monotone_exact x3 h''' T v3;
        bounded_historical_monotone_exact x4 h'''' T v4;
        bounded_historical_monotone_exact x5 h''''' T v5]` by
      simp [bounded_historical_delta_gradient_path_source_contract_def,
            LIST_REL_def]
    >> metis_tac
         [bounded_historical_delta_gradient_coordinate_path_from_source])
  >> irule bounded_historical_delta_gradient_component_contains_scaled_int
  >> simp []
  >> qexistsl_tac
       [`bounded_historical_monotone_coordinate x0 h T`,
        `bounded_historical_monotone_coordinate x1 h' T`,
        `bounded_historical_monotone_coordinate x2 h'' T`,
        `bounded_historical_monotone_coordinate x3 h''' T`,
        `bounded_historical_monotone_coordinate x4 h'''' T`,
        `bounded_historical_monotone_coordinate x5 h''''' T`]
  >> simp [bounded_historical_monotone_exact_selected_contains]
QED

Theorem bounded_historical_delta_gradient_box_shape:
  ∀environment coordinates derivative_rows result.
    bounded_historical_delta_gradient_box
      environment coordinates derivative_rows = SOME result ⇒
    LENGTH coordinates = LENGTH derivative_rows ∧
    LENGTH result = LENGTH coordinates
Proof
  ho_match_mp_tac bounded_historical_delta_gradient_box_ind
  >> rw [bounded_historical_delta_gradient_box_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> simp []
QED

Theorem bounded_historical_delta_gradient_box_list_rel:
  ∀environment coordinates derivative_rows result.
    environment = [x0;x1;x2;x3;x4;x5] ∧
    LIST_REL
      (λcoordinate derivative.
        coordinate < 6 ∧ derivative = EL coordinate rows)
      coordinates derivative_rows ∧
    bounded_historical_delta_gradient_box
      environment coordinates derivative_rows = SOME result ∧
    EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
    LIST_REL bounded_interval64_contains_int
      [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
    bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
    bounded_hessian64_rows hessian = SOME rows ⇒
    LIST_REL
      (λcoordinate value.
        bounded_interval64_contains_scaled_int value
          (&1099511627776:int)
          (bounded_historical_delta_gradient_value
            coordinate v0 v1 v2 v3 v4 v5))
      coordinates result
Proof
  ho_match_mp_tac bounded_historical_delta_gradient_box_ind
  >> rw [bounded_historical_delta_gradient_box_def, LIST_REL_def]
  >> every_case_tac
  >> gvs []
  >> irule bounded_historical_delta_gradient_box_entry_contains_scaled_int
  >> simp [LIST_REL_def]
  >> qexistsl_tac [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
  >> simp [LIST_REL_def]
QED

Theorem bounded_historical_indexed_rows_six:
  LENGTH rows = 6 ⇒
  LIST_REL
    (λcoordinate derivative.
      coordinate < 6 ∧ derivative = EL coordinate rows)
    [0;1;2;3;4;5] rows
Proof
  Cases_on `rows`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs [LIST_REL_def]
QED

Theorem bounded_historical_delta_gradient_box_at_point:
  EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
  LIST_REL bounded_interval64_contains_int
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
  bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
  bounded_hessian64_rows hessian = SOME rows ∧
  bounded_historical_delta_gradient_box [x0;x1;x2;x3;x4;x5]
    [0;1;2;3;4;5] rows = SOME gradient ⇒
  LIST_REL
    (λcoordinate value.
      bounded_interval64_contains_scaled_int value
        (&1099511627776:int)
        (bounded_historical_delta_gradient_value
          coordinate v0 v1 v2 v3 v4 v5))
    [0;1;2;3;4;5] gradient
Proof
  strip_tac
  >> imp_res_tac bounded_historical_delta_gradient_box_shape
  >> `LENGTH rows = 6` by fs []
  >> `LIST_REL
        (λcoordinate derivative.
          coordinate < 6 ∧ derivative = EL coordinate rows)
        [0;1;2;3;4;5] rows` by
      metis_tac [bounded_historical_indexed_rows_six]
  >> metis_tac [bounded_historical_delta_gradient_box_list_rel]
QED

Definition bounded_historical_delta_value_path_endpoint_contract_def:
  bounded_historical_delta_value_path_endpoint_contract upper
      [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [g0;g1;g2;g3;g4;g5] [s0;s1;s2;s3;s4;s5] =
  (s0 = bounded_historical_monotone_exact x0 g0 upper v0 ∧
   s1 = bounded_historical_monotone_exact x1 g1 upper v1 ∧
   s2 = bounded_historical_monotone_exact x2 g2 upper v2 ∧
   s3 = bounded_historical_monotone_exact x3 g3 upper v3 ∧
   s4 = bounded_historical_monotone_exact x4 g4 upper v4 ∧
   s5 = bounded_historical_monotone_exact x5 g5 upper v5 ∧
   bounded_interval64_valid x0 ∧
   bounded_interval64_valid x1 ∧
   bounded_interval64_valid x2 ∧
   bounded_interval64_valid x3 ∧
   bounded_interval64_valid x4 ∧
   bounded_interval64_valid x5 ∧
   bounded_interval64_contains_int x0 v0 ∧
   bounded_interval64_contains_int x1 v1 ∧
   bounded_interval64_contains_int x2 v2 ∧
   bounded_interval64_contains_int x3 v3 ∧
   bounded_interval64_contains_int x4 v4 ∧
   bounded_interval64_contains_int x5 v5 ∧
   bounded_interval64_contains_scaled_int g0 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 0 v0 v1 v2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g0 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 0 s0 v1 v2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g1 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 1 s0 v1 v2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g1 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 1 s0 s1 v2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g2 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 2 s0 s1 v2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g2 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 2 s0 s1 s2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g3 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 3 s0 s1 s2 v3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g3 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 3 s0 s1 s2 s3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g4 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 4 s0 s1 s2 s3 v4 v5) ∧
   bounded_interval64_contains_scaled_int g4 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 4 s0 s1 s2 s3 s4 v5) ∧
   bounded_interval64_contains_scaled_int g5 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 5 s0 s1 s2 s3 s4 v5) ∧
   bounded_interval64_contains_scaled_int g5 (&1099511627776:int)
     (bounded_historical_delta_gradient_value 5 s0 s1 s2 s3 s4 s5)) ∧
  bounded_historical_delta_value_path_endpoint_contract _ _ _ _ _ = F
End

Theorem bounded_historical_delta_value_path_from_endpoints:
  bounded_historical_delta_value_path_endpoint_contract upper
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
    [g0;g1;g2;g3;g4;g5] [s0;s1;s2;s3;s4;s5] ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value s0 s1 s2 s3 s4 s5
  else
    bounded_delta_value s0 s1 s2 s3 s4 s5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  simp_tac (srw_ss())
    [bounded_historical_delta_value_path_endpoint_contract_def]
  >> strip_tac
  >> `if upper then
        bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
        bounded_delta_value s0 v1 v2 v3 v4 v5
      else
        bounded_delta_value s0 v1 v2 v3 v4 v5 ≤
        bounded_delta_value v0 v1 v2 v3 v4 v5` by
       metis_tac [bounded_historical_delta_coordinate_step_zero_from_endpoints]
  >> `if upper then
        bounded_delta_value s0 v1 v2 v3 v4 v5 ≤
        bounded_delta_value s0 s1 v2 v3 v4 v5
      else
        bounded_delta_value s0 s1 v2 v3 v4 v5 ≤
        bounded_delta_value s0 v1 v2 v3 v4 v5` by
       metis_tac [bounded_historical_delta_coordinate_step_one_from_endpoints]
  >> `if upper then
        bounded_delta_value s0 s1 v2 v3 v4 v5 ≤
        bounded_delta_value s0 s1 s2 v3 v4 v5
      else
        bounded_delta_value s0 s1 s2 v3 v4 v5 ≤
        bounded_delta_value s0 s1 v2 v3 v4 v5` by
       metis_tac [bounded_historical_delta_coordinate_step_two_from_endpoints]
  >> `if upper then
        bounded_delta_value s0 s1 s2 v3 v4 v5 ≤
        bounded_delta_value s0 s1 s2 s3 v4 v5
      else
        bounded_delta_value s0 s1 s2 s3 v4 v5 ≤
        bounded_delta_value s0 s1 s2 v3 v4 v5` by
       metis_tac [bounded_historical_delta_coordinate_step_three_from_endpoints]
  >> `if upper then
        bounded_delta_value s0 s1 s2 s3 v4 v5 ≤
        bounded_delta_value s0 s1 s2 s3 s4 v5
      else
        bounded_delta_value s0 s1 s2 s3 s4 v5 ≤
        bounded_delta_value s0 s1 s2 s3 v4 v5` by
       metis_tac [bounded_historical_delta_coordinate_step_four_from_endpoints]
  >> `if upper then
        bounded_delta_value s0 s1 s2 s3 s4 v5 ≤
        bounded_delta_value s0 s1 s2 s3 s4 s5
      else
        bounded_delta_value s0 s1 s2 s3 s4 s5 ≤
        bounded_delta_value s0 s1 s2 s3 s4 v5` by
       metis_tac [bounded_historical_delta_coordinate_step_five_from_endpoints]
  >> Cases_on `upper`
  >> fs []
  >> metis_tac [integerTheory.INT_LE_TRANS]
QED

Definition bounded_historical_delta_value_path_source_contract_def:
  bounded_historical_delta_value_path_source_contract upper
      [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
      [g0;g1;g2;g3;g4;g5] [s0;s1;s2;s3;s4;s5] =
  (s0 = bounded_historical_monotone_exact x0 g0 upper v0 ∧
   s1 = bounded_historical_monotone_exact x1 g1 upper v1 ∧
   s2 = bounded_historical_monotone_exact x2 g2 upper v2 ∧
   s3 = bounded_historical_monotone_exact x3 g3 upper v3 ∧
   s4 = bounded_historical_monotone_exact x4 g4 upper v4 ∧
   s5 = bounded_historical_monotone_exact x5 g5 upper v5 ∧
   EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
   LIST_REL bounded_interval64_contains_int
     [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
   ∃hessian rows.
     bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
     bounded_hessian64_rows hessian = SOME rows ∧
     bounded_historical_delta_gradient_box [x0;x1;x2;x3;x4;x5]
       [0;1;2;3;4;5] rows = SOME [g0;g1;g2;g3;g4;g5]) ∧
  bounded_historical_delta_value_path_source_contract _ _ _ _ _ = F
End

Theorem bounded_historical_delta_value_path_endpoint_contract_from_source:
  bounded_historical_delta_value_path_source_contract upper
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
    [g0;g1;g2;g3;g4;g5] [s0;s1;s2;s3;s4;s5] ⇒
  bounded_historical_delta_value_path_endpoint_contract upper
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
    [g0;g1;g2;g3;g4;g5] [s0;s1;s2;s3;s4;s5]
Proof
  simp_tac (srw_ss())
    [bounded_historical_delta_value_path_source_contract_def,
     LIST_REL_def]
  >> strip_tac
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate v0 v1 v2 v3 v4 v5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def])
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate s0 v1 v2 v3 v4 v5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def]
       >> metis_tac [bounded_historical_monotone_exact_original_contains])
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate s0 s1 v2 v3 v4 v5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def]
       >> metis_tac [bounded_historical_monotone_exact_original_contains])
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate s0 s1 s2 v3 v4 v5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def]
       >> metis_tac [bounded_historical_monotone_exact_original_contains])
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate s0 s1 s2 s3 v4 v5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def]
       >> metis_tac [bounded_historical_monotone_exact_original_contains])
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate s0 s1 s2 s3 s4 v5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def]
       >> metis_tac [bounded_historical_monotone_exact_original_contains])
  >> `LIST_REL
        (λcoordinate value.
          bounded_interval64_contains_scaled_int value
            (&1099511627776:int)
            (bounded_historical_delta_gradient_value
              coordinate s0 s1 s2 s3 s4 s5))
        [0;1;2;3;4;5] [g0;g1;g2;g3;g4;g5]` by
      (irule bounded_historical_delta_gradient_box_at_point
       >> qexistsl_tac
            [`hessian`, `rows`, `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
       >> simp [LIST_REL_def]
       >> metis_tac [bounded_historical_monotone_exact_original_contains])
  >> gvs [bounded_historical_delta_value_path_endpoint_contract_def,
          LIST_REL_def]
QED

Theorem bounded_historical_delta_value_path_from_source:
  bounded_historical_delta_value_path_source_contract upper
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
    [g0;g1;g2;g3;g4;g5] [s0;s1;s2;s3;s4;s5] ⇒
  if upper then
    bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    bounded_delta_value s0 s1 s2 s3 s4 s5
  else
    bounded_delta_value s0 s1 s2 s3 s4 s5 ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5
Proof
  metis_tac
    [bounded_historical_delta_value_path_endpoint_contract_from_source,
     bounded_historical_delta_value_path_from_endpoints]
QED

Theorem bounded_historical_delta64_value_list_rel_contains_scaled_int:
  LIST_REL bounded_interval64_contains_int environment
    [v0;v1;v2;v3;v4;v5] ∧
  bounded_historical_delta64_value environment = SOME result ⇒
  bounded_interval64_contains_scaled_int result
    (&1208925819614629174706176:int)
    (bounded_delta_value v0 v1 v2 v3 v4 v5)
Proof
  Cases_on `environment`
  >> fs [LIST_REL_def]
  >> Cases_on `t`
  >> fs [LIST_REL_def]
  >> Cases_on `t'`
  >> fs [LIST_REL_def]
  >> Cases_on `t`
  >> fs [LIST_REL_def]
  >> Cases_on `t'`
  >> fs [LIST_REL_def]
  >> Cases_on `t`
  >> fs [LIST_REL_def]
  >> Cases_on `t'`
  >> fs [LIST_REL_def]
  >> metis_tac
       [compute_boundedHistoricalDeltaTheory.bounded_historical_delta64_value_contains_scaled_int]
QED

Theorem bounded_historical_delta_extreme_contains_scaled_int:
  EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
  LIST_REL bounded_interval64_contains_int
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
  bounded_delta64_hessian [x0;x1;x2;x3;x4;x5] = SOME hessian ∧
  bounded_hessian64_rows hessian = SOME rows ∧
  bounded_historical_delta_gradient_box [x0;x1;x2;x3;x4;x5]
    [0;1;2;3;4;5] rows = SOME [g0;g1;g2;g3;g4;g5] ∧
  bounded_historical_monotone_environment [x0;x1;x2;x3;x4;x5]
    [g0;g1;g2;g3;g4;g5] F = SOME lower_environment ∧
  bounded_historical_monotone_environment [x0;x1;x2;x3;x4;x5]
    [g0;g1;g2;g3;g4;g5] T = SOME upper_environment ∧
  bounded_historical_delta64_value lower_environment = SOME lower_value ∧
  bounded_historical_delta64_value upper_environment = SOME upper_value ⇒
  bounded_interval64_contains_scaled_int
    (bounded_historical_extreme_interval lower_value upper_value)
    (&1208925819614629174706176:int)
    (bounded_delta_value v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> `LIST_REL bounded_interval64_contains_int lower_environment
        [bounded_historical_monotone_exact x0 g0 F v0;
         bounded_historical_monotone_exact x1 g1 F v1;
         bounded_historical_monotone_exact x2 g2 F v2;
         bounded_historical_monotone_exact x3 g3 F v3;
         bounded_historical_monotone_exact x4 g4 F v4;
         bounded_historical_monotone_exact x5 g5 F v5]` by
      (mp_tac
         (Q.SPECL
           [`[x0;x1;x2;x3;x4;x5]`, `[g0;g1;g2;g3;g4;g5]`,
            `[v0;v1;v2;v3;v4;v5]`, `F`, `lower_environment`]
           bounded_historical_monotone_exact_environment_selected_contains)
       >> simp [bounded_historical_monotone_exact_environment_def])
  >> `LIST_REL bounded_interval64_contains_int upper_environment
        [bounded_historical_monotone_exact x0 g0 T v0;
         bounded_historical_monotone_exact x1 g1 T v1;
         bounded_historical_monotone_exact x2 g2 T v2;
         bounded_historical_monotone_exact x3 g3 T v3;
         bounded_historical_monotone_exact x4 g4 T v4;
         bounded_historical_monotone_exact x5 g5 T v5]` by
      (mp_tac
         (Q.SPECL
           [`[x0;x1;x2;x3;x4;x5]`, `[g0;g1;g2;g3;g4;g5]`,
            `[v0;v1;v2;v3;v4;v5]`, `T`, `upper_environment`]
           bounded_historical_monotone_exact_environment_selected_contains)
       >> simp [bounded_historical_monotone_exact_environment_def])
  >> irule bounded_historical_extreme_interval_contains_scaled_int
  >> conj_tac
  >-
   (qexists_tac
      `bounded_delta_value
          (bounded_historical_monotone_exact x0 g0 F v0)
          (bounded_historical_monotone_exact x1 g1 F v1)
          (bounded_historical_monotone_exact x2 g2 F v2)
          (bounded_historical_monotone_exact x3 g3 F v3)
          (bounded_historical_monotone_exact x4 g4 F v4)
          (bounded_historical_monotone_exact x5 g5 F v5)`
    >> conj_tac
    >-
     (`bounded_historical_delta_value_path_source_contract F
       [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
       [g0;g1;g2;g3;g4;g5]
       [bounded_historical_monotone_exact x0 g0 F v0;
        bounded_historical_monotone_exact x1 g1 F v1;
        bounded_historical_monotone_exact x2 g2 F v2;
        bounded_historical_monotone_exact x3 g3 F v3;
        bounded_historical_monotone_exact x4 g4 F v4;
        bounded_historical_monotone_exact x5 g5 F v5]` by
       simp [bounded_historical_delta_value_path_source_contract_def,
             LIST_REL_def]
      >> metis_tac [bounded_historical_delta_value_path_from_source])
    >> metis_tac
         [bounded_historical_delta64_value_list_rel_contains_scaled_int])
  >> qexists_tac
       `bounded_delta_value
          (bounded_historical_monotone_exact x0 g0 T v0)
          (bounded_historical_monotone_exact x1 g1 T v1)
          (bounded_historical_monotone_exact x2 g2 T v2)
          (bounded_historical_monotone_exact x3 g3 T v3)
          (bounded_historical_monotone_exact x4 g4 T v4)
          (bounded_historical_monotone_exact x5 g5 T v5)`
  >> conj_tac
  >-
   (`bounded_historical_delta_value_path_source_contract T
       [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5]
       [g0;g1;g2;g3;g4;g5]
       [bounded_historical_monotone_exact x0 g0 T v0;
        bounded_historical_monotone_exact x1 g1 T v1;
        bounded_historical_monotone_exact x2 g2 T v2;
        bounded_historical_monotone_exact x3 g3 T v3;
        bounded_historical_monotone_exact x4 g4 T v4;
        bounded_historical_monotone_exact x5 g5 T v5]` by
       simp [bounded_historical_delta_value_path_source_contract_def,
             LIST_REL_def]
    >> metis_tac [bounded_historical_delta_value_path_from_source])
  >> metis_tac
       [bounded_historical_delta64_value_list_rel_contains_scaled_int]
QED

Theorem bounded_historical_delta_second_value_contains_scaled_int:
  EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
  LIST_REL bounded_interval64_contains_int
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
  bounded_historical_delta_second [x0;x1;x2;x3;x4;x5] =
    SOME (delta,gradient,hessian) ⇒
  bounded_interval64_contains_scaled_int delta
    (&1208925819614629174706176:int)
    (bounded_delta_value v0 v1 v2 v3 v4 v5)
Proof
  rw [bounded_historical_delta_second_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac bounded_historical_delta_gradient_box_shape
  >> Cases_on `gradient`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> fs []
  >> Cases_on `t`
  >> fs []
  >> Cases_on `t'`
  >> gvs []
  >> rename1 `bounded_hessian64_rows hessian = SOME rows`
  >> rename1
       `bounded_historical_delta_gradient_box [x0;x1;x2;x3;x4;x5]
          [0;1;2;3;4;5] rows = SOME [g0;g1;g2;g3;g4;g5]`
  >> rename1
       `bounded_historical_monotone_environment [x0;x1;x2;x3;x4;x5]
          [g0;g1;g2;g3;g4;g5] T = SOME upper_environment`
  >> rename1
       `bounded_historical_delta64_value upper_environment =
          SOME upper_value`
  >> rename1
       `bounded_historical_monotone_environment [x0;x1;x2;x3;x4;x5]
          [g0;g1;g2;g3;g4;g5] F = SOME lower_environment`
  >> rename1
       `bounded_historical_delta64_value lower_environment =
          SOME lower_value`
  >> irule bounded_historical_delta_extreme_contains_scaled_int
  >> qexistsl_tac
       [`g0`, `g1`, `g2`, `g3`, `g4`, `g5`, `hessian`,
        `lower_environment`, `rows`, `upper_environment`,
        `x0`, `x1`, `x2`, `x3`, `x4`, `x5`]
  >> simp [LIST_REL_def]
QED

Theorem bounded_historical_delta_second_derivative_components:
  bounded_historical_delta_second environment =
    SOME (delta,gradient,hessian) ⇒
  ∃rows.
    bounded_delta64_hessian environment = SOME hessian ∧
    bounded_hessian64_rows hessian = SOME rows ∧
    bounded_historical_delta_gradient_box environment
      [0;1;2;3;4;5] rows = SOME gradient
Proof
  simp [bounded_historical_delta_second_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
QED

Theorem bounded_historical_delta_second_derivatives_contain:
  EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
  LIST_REL bounded_interval64_contains_int
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
  bounded_historical_delta_second [x0;x1;x2;x3;x4;x5] =
    SOME (delta,gradient,hessian) ⇒
  LIST_REL
    (λcoordinate value.
      bounded_interval64_contains_scaled_int value
        (&1099511627776:int)
        (bounded_historical_delta_gradient_value
          coordinate v0 v1 v2 v3 v4 v5))
    [0;1;2;3;4;5] gradient ∧
  ∃rows.
    bounded_hessian64_rows hessian = SOME rows ∧
    LIST_REL (LIST_REL bounded_interval64_contains_int) rows
      (bounded_delta_hessian_value_matrix v0 v1 v2 v3 v4 v5)
Proof
  strip_tac
  >> imp_res_tac bounded_historical_delta_second_derivative_components
  >> conj_tac
  >-
   (mp_tac
      (Q.SPECL
         [`x5`, `x4`, `x3`, `x2`, `x1`, `x0`,
          `v5`, `v4`, `v3`, `v2`, `v1`, `v0`,
          `rows`, `hessian`, `gradient`]
         (GEN_ALL bounded_historical_delta_gradient_box_at_point))
    >> simp [LIST_REL_def])
  >> qexists_tac `rows`
  >> conj_tac
  >- simp []
  >> mp_tac
       (Q.SPECL
          [`x5`, `x4`, `x3`, `x2`, `x1`, `x0`,
           `v5`, `v4`, `v3`, `v2`, `v1`, `v0`, `rows`, `hessian`]
          (GEN_ALL bounded_historical_delta_hessian_rows_contains_ints))
  >> disch_then irule
  >> fs [LIST_REL_def]
QED

Theorem bounded_historical_sqrt_hessian_lengths:
  ∀indices hessian result derivative logarithmic_derivative gradient.
    bounded_historical_sqrt_hessian derivative logarithmic_derivative
      gradient indices hessian = SOME result ⇒
    LENGTH result = LENGTH indices ∧ LENGTH result = LENGTH hessian
Proof
  Induct
  >- (Cases_on `hessian`
      >> simp [bounded_historical_sqrt_hessian_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `hessian`
  >- simp [bounded_historical_sqrt_hessian_def]
  >> simp [bounded_historical_sqrt_hessian_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
  >> res_tac
  >> fs []
QED

Theorem bounded_historical_sqrt_second_components:
  bounded_historical_sqrt_second value gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    SOME (result_value,result_gradient,result_hessian) ⇒
  result_value = root ∧
  bounded_interval64_sqrt_certificate value root ∧
  ∃twice_root twice_value.
    bounded_historical_scale2 root = SOME twice_root ∧
    bounded_interval64_inv_certificate
      twice_root derivative_reciprocal ∧
    bounded_historical_scale2 value = SOME twice_value ∧
    bounded_interval64_inv_certificate
      twice_value logarithmic_reciprocal ∧
    bounded_interval64_list_scale derivative_reciprocal gradient =
      SOME result_gradient ∧
    bounded_historical_sqrt_hessian derivative_reciprocal
      (bounded_interval64_neg logarithmic_reciprocal) gradient
      bounded_delta64_hessian_indices hessian = SOME result_hessian
Proof
  simp [bounded_historical_sqrt_second_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
QED

Theorem bounded_historical_sqrt_second_shape:
  bounded_historical_sqrt_second value gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    SOME (result_value,result_gradient,result_hessian) ⇒
  result_value = root ∧
  LENGTH result_gradient = LENGTH gradient ∧
  LENGTH hessian = 21 ∧ LENGTH result_hessian = 21
Proof
  strip_tac
  >> imp_res_tac bounded_historical_sqrt_second_components
  >> imp_res_tac
       compute_boundedIntervalListTheory.bounded_interval64_list_scale_length
  >> imp_res_tac bounded_historical_sqrt_hessian_lengths
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def]
QED

Theorem bounded_historical_delta_sqrt_second_value_square_contains:
  EVERY bounded_interval64_valid [x0;x1;x2;x3;x4;x5] ∧
  LIST_REL bounded_interval64_contains_int
    [x0;x1;x2;x3;x4;x5] [v0;v1;v2;v3;v4;v5] ∧
  bounded_historical_delta_second [x0;x1;x2;x3;x4;x5] =
    SOME (delta,gradient,hessian) ∧
  bounded_historical_sqrt_second delta gradient hessian root
      derivative_reciprocal logarithmic_reciprocal =
    SOME (result_value,result_gradient,result_hessian) ⇒
  (&1099511627776:int) *
      bounded_signed64_to_int
        (bounded_interval64_lower result_value) *
      bounded_signed64_to_int
        (bounded_interval64_lower result_value) ≤
    bounded_delta_value v0 v1 v2 v3 v4 v5 ∧
  bounded_delta_value v0 v1 v2 v3 v4 v5 ≤
    (&1099511627776:int) *
      bounded_signed64_to_int
        (bounded_interval64_upper result_value) *
      bounded_signed64_to_int
        (bounded_interval64_upper result_value)
Proof
  strip_tac
  >> imp_res_tac bounded_historical_delta_second_value_contains_scaled_int
  >> imp_res_tac bounded_historical_sqrt_second_components
  >> metis_tac
       [compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_contains_scaled_square]
QED

Theorem bounded_historical_replace_three_length:
  bounded_historical_replace_three values replacement = SOME result ⇒
  LENGTH result = 6
Proof
  rw [compute_boundedHistoricalDihedralFirstTheory.bounded_historical_replace_three_def]
  >> every_case_tac
  >> gvs []
QED

Theorem bounded_historical_second_hessian_lengths:
  ∀indices delta_hessian b_hessian result delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient.
    bounded_historical_second_hessian delta_x4 b reciprocal_u
      delta_x4_gradient b_gradient result_gradient logarithmic_u_gradient
      indices delta_hessian b_hessian = SOME result ⇒
    LENGTH result = LENGTH indices ∧
    LENGTH result = LENGTH delta_hessian ∧
    LENGTH result = LENGTH b_hessian
Proof
  Induct
  >- (Cases_on `delta_hessian`
      >> Cases_on `b_hessian`
      >> simp [bounded_historical_second_hessian_def])
  >> rpt gen_tac
  >> PairCases_on `h`
  >> Cases_on `delta_hessian`
  >- simp [bounded_historical_second_hessian_def]
  >> Cases_on `b_hessian`
  >- simp [bounded_historical_second_hessian_def]
  >> simp [bounded_historical_second_hessian_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
  >> res_tac
  >> fs []
QED

Theorem bounded_interval64_contains_int_scale_squared:
  bounded_interval64_contains_int interval value ⇒
  bounded_interval64_contains_scaled_int interval
    (&1208925819614629174706176:int)
    ((&1208925819614629174706176:int) * value)
Proof
  Cases_on `interval`
  >> fs [compute_boundedIntervalTheory.bounded_interval64_contains_int_def,
         compute_boundedIntervalTheory.bounded_interval64_contains_scaled_int_def]
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_root_four_square_contains:
  bounded_interval64_contains_int x0 v0 ∧
  bounded_interval64_scale4 x0 = SOME four_x0 ∧
  bounded_interval64_sqrt_certificate four_x0 root_four_x0 ⇒
  (&1099511627776:int) *
      bounded_signed64_to_int (bounded_interval64_lower root_four_x0) *
      bounded_signed64_to_int (bounded_interval64_lower root_four_x0) ≤
    (&1208925819614629174706176:int) * (4 * v0) ∧
  (&1208925819614629174706176:int) * (4 * v0) ≤
    (&1099511627776:int) *
      bounded_signed64_to_int (bounded_interval64_upper root_four_x0) *
      bounded_signed64_to_int (bounded_interval64_upper root_four_x0)
Proof
  strip_tac
  >> `bounded_interval64_contains_scaled_int x0
        (&1208925819614629174706176:int)
        ((&1208925819614629174706176:int) * v0)` by
       metis_tac [bounded_interval64_contains_int_scale_squared]
  >> `bounded_interval64_contains_scaled_int four_x0
        (&1208925819614629174706176:int)
        (4 * ((&1208925819614629174706176:int) * v0))` by
       metis_tac
         [compute_boundedDeltaTaylorTheory.bounded_interval64_scale4_contains_scaled_int]
  >> imp_res_tac
       compute_boundedSqrtCertificateTheory.bounded_interval64_sqrt_certificate_contains_scaled_square
  >> intLib.ARITH_TAC
QED

Theorem bounded_historical_dihedral_second64_root_product_contract:
  bounded_historical_dihedral_second64 environment root_delta root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ⇒
  ∃delta delta_gradient delta_hessian root_value root_gradient root_hessian
      x0 four_x0 b.
    bounded_historical_delta_second environment =
      SOME (delta,delta_gradient,delta_hessian) ∧
    bounded_historical_sqrt_second delta delta_gradient delta_hessian
      root_delta root_derivative root_logarithmic =
      SOME (root_value,root_gradient,root_hessian) ∧
    bounded_interval64_nth environment 0 = SOME x0 ∧
    bounded_interval64_scale4 x0 = SOME four_x0 ∧
    bounded_interval64_sqrt_certificate four_x0 root_four_x0 ∧
    bounded_interval64_inv_certificate
      root_four_x0 root_four_reciprocal ∧
    bounded_interval64_mul root_delta root_four_x0 = SOME b ∧
    bounded_interval64_inv_certificate b b_reciprocal
Proof
  simp [bounded_historical_dihedral_second64_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
  >> metis_tac []
QED

Theorem bounded_historical_dihedral_second64_root_product_contains:
  bounded_interval64_contains_int root_delta root_delta_value ∧
  bounded_interval64_contains_int root_four_x0 root_four_x0_value ∧
  bounded_historical_dihedral_second64 environment root_delta root_four_x0
      [root_derivative;root_logarithmic;root_four_reciprocal;
       diagonal_reciprocal;u_reciprocal;special_root_reciprocal;
       b_reciprocal;u126_reciprocal;u135_reciprocal] =
    SOME (value,gradient,hessian) ⇒
  ∃b.
    bounded_interval64_inv_certificate b b_reciprocal ∧
    bounded_interval64_contains_scaled_int b
      (&1099511627776:int) (root_delta_value * root_four_x0_value)
Proof
  strip_tac
  >> imp_res_tac
       bounded_historical_dihedral_second64_root_product_contract
  >> qexists_tac `b`
  >> conj_tac
  >- fs []
  >> metis_tac
       [compute_boundedIntervalTheory.bounded_interval64_mul_contains_scaled_product]
QED

Theorem bounded_historical_dihedral_second64_rejects_bad_reciprocal_length:
  LENGTH reciprocal_certificates ≠ 9 ⇒
  bounded_historical_dihedral_second64 environment root_delta root_four_x0
      reciprocal_certificates = NONE
Proof
  simp [bounded_historical_dihedral_second64_def]
  >> every_case_tac
  >> fs []
QED

Theorem bounded_historical_dihedral_second64_shape:
  bounded_historical_dihedral_second64 environment root_delta root_four_x0
      reciprocal_certificates = SOME (value,gradient,hessian) ⇒
  LENGTH gradient = 6 ∧ LENGTH hessian = 21
Proof
  simp [bounded_historical_dihedral_second64_def]
  >> rpt (TOP_CASE_TAC >> gvs [])
  >> strip_tac
  >> gvs []
  >> imp_res_tac bounded_historical_replace_three_length
  >> imp_res_tac bounded_historical_second_hessian_lengths
  >> fs [compute_boundedDeltaTaylorTheory.bounded_delta64_hessian_indices_def]
QED

val _ = export_theory ();
