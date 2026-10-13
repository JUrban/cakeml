(*****************************************************************************
 * Streaming fail-closed boundary for a complete varied case-10173 batch.
 *
 * Each fixed-width packet is parsed from ordinary untrusted bytes and passed
 * to the already proved complete word checker.  Parsing is sequential so the
 * full 4,173-cell fixture need not be expanded into thousands of HOL
 * definitions or retained as a decoded list.
 *****************************************************************************)
Theory compute_boundedCase10173PackedBatch
Ancestors
  compute_boundedCase10173Packet compute_boundedPackedSequentialInput
Libs
  bossLib preamble wordsLib

Definition bounded_packed_chars_interval64_list_def:
  bounded_packed_chars_interval64_list 0 bytes = SOME ([],bytes) /\
  bounded_packed_chars_interval64_list (SUC remaining) bytes =
    case bounded_packed_chars_interval64 bytes of
    | NONE => NONE
    | SOME (value,rest) =>
      case bounded_packed_chars_interval64_list remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (value::suffix,finish)
End

Theorem bounded_packed_chars_interval64_list_length:
  !count bytes values rest.
    bounded_packed_chars_interval64_list count bytes = SOME (values,rest) ==>
    LENGTH values = count
Proof
  Induct
  >> rw [bounded_packed_chars_interval64_list_def]
  >> every_case_tac
  >> res_tac
  >> gvs []
QED

Theorem bounded_packed_chars_interval64_list_two_shape:
  bounded_packed_chars_interval64_list 2 bytes = SOME (values,rest) ==>
  ?a b. values = [a;b]
Proof
  strip_tac
  >> drule bounded_packed_chars_interval64_list_length
  >> simp []
  >> disch_tac
  >> Cases_on `values`
  >> gvs []
  >> Cases_on `t`
  >> gvs []
  >> Cases_on `t'`
  >> gvs []
QED

Definition bounded_packed_chars_case10173_sqrt64_certificate_def:
  bounded_packed_chars_case10173_sqrt64_certificate bytes =
    case bounded_packed_chars_interval64_list 5 bytes of
    | SOME ([center_root;box_root;center_derivative;box_derivative;
             second_derivative],finish) =>
        SOME (BoundedCase10173Sqrt64Certificate center_root box_root
          center_derivative box_derivative second_derivative,finish)
    | _ => NONE
End

Definition bounded_packed_chars_case10173_sqrt64_certificate_list_def:
  bounded_packed_chars_case10173_sqrt64_certificate_list 0 bytes =
      SOME ([],bytes) /\
  bounded_packed_chars_case10173_sqrt64_certificate_list (SUC remaining)
      bytes =
    case bounded_packed_chars_case10173_sqrt64_certificate bytes of
    | NONE => NONE
    | SOME (certificate,rest) =>
      case bounded_packed_chars_case10173_sqrt64_certificate_list
          remaining rest of
      | NONE => NONE
      | SOME (suffix,finish) => SOME (certificate::suffix,finish)
End

Definition bounded_packed_chars_case10173_packet_def:
  bounded_packed_chars_case10173_packet bytes =
    case bounded_packed_chars_word64_list 6 bytes of
    | NONE => NONE
    | SOME (radii,rest1) =>
      case bounded_packed_chars_interval64_list 6 rest1 of
      | NONE => NONE
      | SOME (center_environment,rest2) =>
        case bounded_packed_chars_interval64_list 6 rest2 of
        | NONE => NONE
        | SOME (box_environment,rest3) =>
          case bounded_packed_chars_case10173_sqrt64_certificate_list
              6 rest3 of
          | NONE => NONE
          | SOME (coordinate_sqrt_certificates,rest4) =>
            case bounded_packed_chars_interval64_list 2 rest4 of
            | NONE => NONE
            | SOME (center_roots,rest5) =>
              case center_roots of
              | [center_root_delta;center_root_four_x0] =>
                case bounded_packed_chars_interval64_list 5 rest5 of
                | NONE => NONE
                | SOME (center_reciprocals,rest6) =>
                  case bounded_packed_chars_interval64_list 2 rest6 of
                  | NONE => NONE
                  | SOME (box_roots,rest7) =>
                    case box_roots of
                    | [box_root_delta;box_root_four_x0] =>
                      case bounded_packed_chars_interval64_list 9 rest7 of
                      | NONE => NONE
                      | SOME (box_reciprocals,finish) =>
                        SOME
                          (BoundedCase10173Packet radii center_environment
                            box_environment coordinate_sqrt_certificates
                            center_root_delta center_root_four_x0
                            center_reciprocals box_root_delta box_root_four_x0
                            box_reciprocals,finish)
                    | _ => NONE
              | _ => NONE
End

Definition bounded_packed_chars_case10173_packet_ok_def:
  bounded_packed_chars_case10173_packet_ok packet <=>
    bounded_case10173_packet_accepts packet
End

Definition bounded_packed_chars_case10173_packets_def:
  bounded_packed_chars_case10173_packets 0 bytes count =
      (if bytes = [] then SOME count else NONE) /\
  bounded_packed_chars_case10173_packets (SUC remaining) bytes count =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => NONE
    | SOME (packet,rest) =>
        if bounded_packed_chars_case10173_packet_ok packet then
          bounded_packed_chars_case10173_packets remaining rest (SUC count)
        else NONE
End

Definition bounded_packed_chars_case10173_full_header_def:
  bounded_packed_chars_case10173_full_header bytes =
    case bounded_packed_chars_prefix
      [#"C";#"N";#"L";#"C";#"P";#"B";#"0";#"1"] bytes of
    | NONE => NONE
    | SOME rest =>
      case bounded_packed_chars_word64_aux 4 rest of
      | NONE => NONE
      | SOME (cells,finish) =>
          if cells = 4173w then SOME finish else NONE
End

Definition bounded_packed_chars_case10173_full_check_def:
  bounded_packed_chars_case10173_full_check bytes <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_packets 4173 rest 0 = SOME 4173
End

Theorem bounded_packed_chars_case10173_full_check_truncated:
  ~bounded_packed_chars_case10173_full_check []
Proof
  EVAL_TAC
QED

Theorem bounded_packed_chars_case10173_full_check_bad_count:
  ~bounded_packed_chars_case10173_full_check
    [#"C";#"N";#"L";#"C";#"P";#"B";#"0";#"1";
     CHR 3;CHR 0;CHR 0;CHR 0]
Proof
  EVAL_TAC >> wordsLib.WORD_EVAL_TAC
QED

val _ = export_theory ();
