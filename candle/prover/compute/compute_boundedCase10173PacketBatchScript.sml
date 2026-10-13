(*****************************************************************************
 * Fail-closed batch boundary for complete case-10173 numerical packets.
 *
 * Packet data remains ordinary untrusted cv input.  Every element is decoded
 * with the canonical single-packet decoder and then recomputed by the complete
 * checked-word cell predicate.  The list encoding is exact: Num 0 is nil,
 * Pair is cons, and every other shape is rejected.
 *****************************************************************************)
Theory compute_boundedCase10173PacketBatch
Ancestors
  compute_boundedCase10173Packet
Libs
  bossLib preamble

val _ = monadsyntax.temp_enable_monad "option";

Definition bounded_cv_encode_case10173_packet_list_def:
  bounded_cv_encode_case10173_packet_list [] = (Num 0 : cv) /\
  bounded_cv_encode_case10173_packet_list (packet::packets) =
    Pair (bounded_cv_encode_case10173_packet packet)
      (bounded_cv_encode_case10173_packet_list packets)
End

Definition bounded_cv_decode_case10173_packet_list_def:
  bounded_cv_decode_case10173_packet_list (Num 0 : cv) = SOME [] /\
  bounded_cv_decode_case10173_packet_list (Pair packet packets) =
    do
      packet' <- bounded_cv_decode_case10173_packet packet;
      packets' <- bounded_cv_decode_case10173_packet_list packets;
      return (packet'::packets')
    od /\
  bounded_cv_decode_case10173_packet_list _ = NONE
Termination
  wf_rel_tac `measure cv_size` >> rw []
End

Definition bounded_case10173_packet_batch_accepts_def:
  bounded_case10173_packet_batch_accepts [] = T /\
  bounded_case10173_packet_batch_accepts (packet::packets) =
    (bounded_case10173_packet_accepts packet /\
     bounded_case10173_packet_batch_accepts packets)
End

Definition bounded_case10173_packet_batch_check_cv_def:
  bounded_case10173_packet_batch_check_cv payload =
    case bounded_cv_decode_case10173_packet_list payload of
    | NONE => NONE
    | SOME packets =>
        SOME (bounded_cv_encode_bool
          (bounded_case10173_packet_batch_accepts packets))
End

Theorem bounded_cv_decode_case10173_packet_list_encode_exact:
  !packets.
    bounded_cv_decode_case10173_packet_list
      (bounded_cv_encode_case10173_packet_list packets) =
    if EVERY bounded_case10173_packet_well_shaped packets
    then SOME packets
    else NONE
Proof
  Induct
  >> simp [bounded_cv_decode_case10173_packet_list_def,
           bounded_cv_encode_case10173_packet_list_def,
           compute_boundedCase10173PacketTheory.bounded_cv_decode_case10173_packet_encode_exact]
  >> rpt gen_tac
  >> Cases_on `bounded_case10173_packet_well_shaped h`
  >> Cases_on `EVERY bounded_case10173_packet_well_shaped packets`
  >> simp []
QED

Theorem bounded_case10173_packet_batch_check_cv_accepts:
  EVERY bounded_case10173_packet_well_shaped packets /\
  bounded_case10173_packet_batch_accepts packets ==>
  bounded_case10173_packet_batch_check_cv
      (bounded_cv_encode_case10173_packet_list packets) = SOME (Num 1)
Proof
  simp [bounded_case10173_packet_batch_check_cv_def,
        bounded_cv_decode_case10173_packet_list_encode_exact,
        compute_boundedCase10173PacketTheory.bounded_cv_encode_bool_def]
QED

Theorem bounded_case10173_packet_batch_check_cv_rejects_bad_shape:
  ~EVERY bounded_case10173_packet_well_shaped packets ==>
  bounded_case10173_packet_batch_check_cv
      (bounded_cv_encode_case10173_packet_list packets) = NONE
Proof
  strip_tac
  >> `bounded_cv_decode_case10173_packet_list
        (bounded_cv_encode_case10173_packet_list packets) = NONE`
       by rw [bounded_cv_decode_case10173_packet_list_encode_exact]
  >> simp [bounded_case10173_packet_batch_check_cv_def]
QED

Theorem bounded_case10173_packet_batch_check_cv_rejects_nonlist:
  n <> 0 ==>
  bounded_case10173_packet_batch_check_cv (Num n) = NONE
Proof
  Cases_on `n`
  >> simp [bounded_case10173_packet_batch_check_cv_def,
           bounded_cv_decode_case10173_packet_list_def]
QED

val _ = export_theory ();
