(*****************************************************************************
 * Development batch requiring both the optimized verdict and the exact
 * source-shaped bounded verdict.  This is deliberately separate from the
 * production batch while its acceptance and performance are measured.
 *****************************************************************************)
Theory compute_boundedCase10173PackedDecimalLiteralBatch
Ancestors
  compute_boundedCase10173PackedDecimalBatch
  compute_boundedCase10173LiteralSourceDecimal
Libs
  bossLib preamble

Definition bounded_packed_chars_case10173_decimal_literal_packets_def:
  bounded_packed_chars_case10173_decimal_literal_packets 0 bytes count =
      (if bytes = [] then SOME count else NONE) /\
  bounded_packed_chars_case10173_decimal_literal_packets
      (SUC remaining) bytes count =
    case bounded_packed_chars_case10173_packet bytes of
    | NONE => NONE
    | SOME (packet,rest) =>
        if bounded_packed_chars_case10173_decimal_packet_ok packet /\
           bounded_case10173_literal_source_accepts_decimal packet
        then bounded_packed_chars_case10173_decimal_literal_packets
          remaining rest (SUC count)
        else NONE
End

Definition bounded_packed_chars_case10173_decimal_literal_full_check_def:
  bounded_packed_chars_case10173_decimal_literal_full_check bytes <=>
    case bounded_packed_chars_case10173_full_header bytes of
    | NONE => F
    | SOME rest =>
        bounded_packed_chars_case10173_decimal_literal_packets
          4173 rest 0 = SOME 4173
End

Theorem bounded_packed_chars_case10173_decimal_literal_packets_numerical:
  !remaining bytes count result.
    bounded_packed_chars_case10173_decimal_literal_packets
      remaining bytes count = SOME result ==>
    bounded_packed_chars_case10173_decimal_packets
      remaining bytes count = SOME result
Proof
  Induct
  >> rw
       [bounded_packed_chars_case10173_decimal_literal_packets_def,
        compute_boundedCase10173PackedDecimalBatchTheory.bounded_packed_chars_case10173_decimal_packets_def]
  >> every_case_tac
  >> gvs []
  >> res_tac
  >> gvs []
QED

val _ = export_theory ();
