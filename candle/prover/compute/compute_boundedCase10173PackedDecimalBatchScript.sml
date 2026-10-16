(*****************************************************************************
 * Streaming strengthened-decimal checker for the complete case-10173 batch.
 *
 * The byte layout is shared with the earlier packed checker, but every packet
 * is consumed by the canonical scale-10^12 checker.  Successful source
 * acceptance is lifted pointwise to the exact object-level Taylor verdict;
 * the batch contract therefore records all object verdicts without retaining
 * a decoded 4,173-element list.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalBatch
Ancestors
  compute_boundedCase10173PackedBatch
  compute_boundedObjectCase10173HistoricalCellDecimal
Libs
  bossLib preamble wordsLib

Definition bounded_packed_chars_case10173_decimal_packet_ok_def:
  bounded_packed_chars_case10173_decimal_packet_ok
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
    case center_reciprocals of
    | [center_root_derivative;center_root_four_reciprocal;
       center_u_reciprocal;center_special_root_reciprocal;
       center_b_reciprocal] =>
      (case box_reciprocals of
      | [box_root_derivative;box_root_logarithmic;
         box_root_four_reciprocal;box_diagonal_reciprocal;
         box_u_reciprocal;box_special_root_reciprocal;
         box_b_reciprocal;box_u126_reciprocal;box_u135_reciprocal] =>
          bounded_case10173_checked_cell_accepts_decimal radii
            center_environment box_environment coordinate_sqrt_certificates
            center_root_delta center_root_four_x0 center_reciprocals
            box_root_delta box_root_four_x0 box_reciprocals
      | _ => F)
    | _ => F
End

Definition bounded_packed_chars_case10173_decimal_packet_object_ok_def:
  bounded_packed_chars_case10173_decimal_packet_object_ok
      (BoundedCase10173Packet radii center_environment box_environment
        coordinate_sqrt_certificates center_root_delta center_root_four_x0
        center_reciprocals box_root_delta box_root_four_x0 box_reciprocals) <=>
    ?center_value center_gradient value_bound gradient_bounds hessian
     hessian_rows.
      bounded_object_case10173_checked_cell64_decimal radii
        center_environment box_environment coordinate_sqrt_certificates
        center_root_delta center_root_four_x0 center_reciprocals
        box_root_delta box_root_four_x0 box_reciprocals =
          SOME
            (bounded_taylor64_rows_object_cv
              (BoundedTaylor64 T center_value center_gradient value_bound
                gradient_bounds hessian) hessian_rows) /\
      bounded_signed64_strict_negative
        (bounded_interval64_upper value_bound)
End

Theorem bounded_packed_chars_case10173_decimal_packet_ok_object_sound:
  bounded_packed_chars_case10173_decimal_packet_ok packet ==>
  bounded_packed_chars_case10173_decimal_packet_object_ok packet
Proof
  Cases_on `packet`
  >> rw
       [bounded_packed_chars_case10173_decimal_packet_ok_def,
        bounded_packed_chars_case10173_decimal_packet_object_ok_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       compute_boundedObjectCase10173HistoricalCellDecimalTheory.bounded_object_case10173_checked_cell_accepts_decimal_exact
  >> metis_tac []
QED

Definition bounded_packed_chars_case10173_decimal_packets_def:
  bounded_packed_chars_case10173_decimal_packets 0 bytes count =
      (if bytes = [] then SOME count else NONE) /\
  bounded_packed_chars_case10173_decimal_packets (SUC remaining) bytes count =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => NONE
    | SOME (packet,rest) =>
        if bounded_packed_chars_case10173_decimal_packet_ok packet then
          bounded_packed_chars_case10173_decimal_packets
            remaining rest (SUC count)
        else NONE
End

Definition bounded_packed_chars_case10173_decimal_object_packets_def:
  bounded_packed_chars_case10173_decimal_object_packets 0 bytes =
      (bytes = []) /\
  bounded_packed_chars_case10173_decimal_object_packets (SUC remaining)
      bytes =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => F
    | SOME (packet,rest) =>
        bounded_packed_chars_case10173_decimal_packet_object_ok packet /\
        bounded_packed_chars_case10173_decimal_object_packets remaining rest
End

Theorem bounded_packed_chars_case10173_decimal_packets_object_sound:
  !bytes count result.
    bounded_packed_chars_case10173_decimal_packets remaining bytes count =
      SOME result ==>
    bounded_packed_chars_case10173_decimal_object_packets remaining bytes
Proof
  Induct_on `remaining`
  >> rw
       [bounded_packed_chars_case10173_decimal_packets_def,
        bounded_packed_chars_case10173_decimal_object_packets_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_packet_ok_object_sound
  >> res_tac
  >> gvs []
QED

Definition bounded_packed_chars_case10173_decimal_full_check_def:
  bounded_packed_chars_case10173_decimal_full_check bytes <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_decimal_packets
          4173 rest 0 = SOME 4173
End

Definition bounded_packed_chars_case10173_decimal_full_object_contract_def:
  bounded_packed_chars_case10173_decimal_full_object_contract bytes <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_decimal_object_packets 4173 rest
End

Theorem bounded_packed_chars_case10173_decimal_full_check_object_sound:
  bounded_packed_chars_case10173_decimal_full_check bytes ==>
  bounded_packed_chars_case10173_decimal_full_object_contract bytes
Proof
  rw
    [bounded_packed_chars_case10173_decimal_full_check_def,
     bounded_packed_chars_case10173_decimal_full_object_contract_def]
  >> every_case_tac
  >> gvs []
  >> imp_res_tac
       bounded_packed_chars_case10173_decimal_packets_object_sound
QED

Theorem bounded_packed_chars_case10173_decimal_full_check_truncated:
  ~bounded_packed_chars_case10173_decimal_full_check []
Proof
  EVAL_TAC
QED

val _ = export_theory ();
