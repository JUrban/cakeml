(* One-cell development discriminator for the second-order checker. *)
Theory compute_boundedHistoricalDihedralSecondStatus
Ancestors
  compute_boundedHistoricalDihedralSecondPackedCheck
Libs
  bossLib preamble

(*
 * Distinguish the certificate-producing prefix from later arithmetic.  This
 * is deliberately a development-only observer: it recomputes the same
 * authenticated inputs but does not weaken the Boolean release checker.
 *)
Definition bounded_historical_dihedral_second_certificate_stage_def:
  bounded_historical_dihedral_second_certificate_stage environment
      root_delta root_four_x0 reciprocal_certificates =
    case reciprocal_certificates of
    | root_derivative::root_logarithmic::root_four_reciprocal::
        diagonal_reciprocal::u_reciprocal::special_root_reciprocal::
        b_reciprocal::u126_reciprocal::u135_reciprocal::[] =>
      case bounded_historical_delta_second environment of
      | NONE => (10:num)
      | SOME (delta,delta_gradient,delta_hessian) =>
        case bounded_historical_sqrt_second
          delta delta_gradient delta_hessian root_delta
          root_derivative root_logarithmic of
        | NONE => 11
        | SOME _ =>
          case bounded_historical_delta_x4_second environment of
          | NONE => 12
          | SOME _ =>
            case bounded_historical_u126 environment of
            | NONE => 13
            | SOME (u126,_) =>
              case bounded_historical_u135 environment of
              | NONE => 14
              | SOME (u135,_) =>
                case bounded_interval64_nth environment 0 of
                | NONE => 15
                | SOME x0 =>
                  case bounded_interval64_scale4 x0 of
                  | NONE => 16
                  | SOME four_x0 =>
                    if ¬bounded_interval64_sqrt_certificate
                      four_x0 root_four_x0 then 17
                    else if ¬bounded_interval64_inv_certificate
                      root_four_x0 root_four_reciprocal then 18
                    else
                      case bounded_historical_scale2 x0 of
                      | NONE => 19
                      | SOME twice_x0 =>
                        if ¬bounded_interval64_inv_certificate
                          twice_x0 diagonal_reciprocal then 20
                        else
                          case bounded_interval64_mul
                            root_delta root_four_x0 of
                          | NONE => 21
                          | SOME b =>
                            if ¬bounded_interval64_inv_certificate
                              b b_reciprocal then 22
                            else
                              case bounded_interval64_mul u126 u135 of
                              | NONE => 23
                              | SOME u_product =>
                                if ¬bounded_interval64_inv_certificate
                                  u_product u_reciprocal then 24
                                else if ¬bounded_interval64_inv_certificate
                                  u126 u126_reciprocal then 25
                                else if ¬bounded_interval64_inv_certificate
                                  u135 u135_reciprocal then 26
                                else
                                  case bounded_historical_scale2
                                    root_delta of
                                  | NONE => 27
                                  | SOME twice_root_delta =>
                                    if ¬bounded_interval64_inv_certificate
                                      twice_root_delta
                                      special_root_reciprocal
                                    then 28
                                    else 29
    | _ => 9
End

Definition bounded_packed_historical_second_cell_status_def:
  bounded_packed_historical_second_cell_status values =
    case values of
    | e0::e1::e2::e3::e4::e5::root_delta::root_four_x0::
        r0::r1::r2::r3::r4::r5::r6::r7::r8::expected_value::
        g0::g1::g2::g3::g4::g5::
        h00::h01::h02::h03::h04::h05::
        h11::h12::h13::h14::h15::
        h22::h23::h24::h25::
        h33::h34::h35::h44::h45::h55::[] =>
      (case bounded_historical_dihedral_second64
        [e0;e1;e2;e3;e4;e5] root_delta root_four_x0
        [r0;r1;r2;r3;r4;r5;r6;r7;r8] of
      | NONE =>
          bounded_historical_dihedral_second_certificate_stage
            [e0;e1;e2;e3;e4;e5] root_delta root_four_x0
            [r0;r1;r2;r3;r4;r5;r6;r7;r8]
      | SOME (value,gradient,hessian) =>
        if value ≠ expected_value then (2:num)
        else if gradient ≠ [g0;g1;g2;g3;g4;g5] then 3
        else if hessian ≠
          [h00;h01;h02;h03;h04;h05;
           h11;h12;h13;h14;h15;
           h22;h23;h24;h25;
           h33;h34;h35;h44;h45;h55]
        then 4
        else 0)
    | _ => 5
End

Definition bounded_packed_chars_historical_second_status_def:
  bounded_packed_chars_historical_second_status bytes =
    case bounded_packed_chars_historical_second_header bytes of
    | SOME (1,rest) =>
      (case bounded_packed_chars_historical_second_cell rest of
       | SOME (cell,[]) => bounded_packed_historical_second_cell_status cell
       | _ => 5)
    | _ => 5
End

val _ = export_theory ();
