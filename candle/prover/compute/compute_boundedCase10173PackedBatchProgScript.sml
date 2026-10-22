(* CakeML translation of the complete packed varied case-10173 checker. *)
Theory compute_boundedCase10173PackedBatchProg
Ancestors
  compute_boundedCase10173PacketProg
  compute_boundedCase10173PackedBatch
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase10173PacketProg";

(* The packet-program lineage already contains the full checked numerical
   engine.  Add only the reusable sequential-byte substrate and the new
   fixed-width packet fold. *)
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_aux_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_signed64_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_interval64_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_word64_list_def;
val _ = translate
  compute_boundedPackedSequentialInputTheory.bounded_packed_chars_prefix_def;

val _ = translate bounded_packed_chars_interval64_list_def;
val _ = translate bounded_packed_chars_case10173_sqrt64_certificate_def;
val _ = translate
  bounded_packed_chars_case10173_sqrt64_certificate_list_def;
val _ = translate bounded_packed_chars_case10173_packet_def;

Theorem bounded_packed_chars_case10173_packet_side_total[local]:
  !bytes. bounded_packed_chars_case10173_packet_side bytes
Proof
  rw [fetch "-" "bounded_packed_chars_case10173_packet_side_def"]
  >> imp_res_tac
       compute_boundedCase10173PackedBatchTheory.bounded_packed_chars_interval64_list_two_shape
  >> gvs []
QED

val _ = bounded_packed_chars_case10173_packet_side_total
  |> update_precondition;

val _ = translate bounded_packed_chars_case10173_packet_ok_def;
val _ = translate bounded_packed_chars_case10173_packets_def;
val _ = translate bounded_packed_chars_case10173_full_header_def;
val _ = translate bounded_packed_chars_case10173_full_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_case10173_full_check (String.explode payload)
    then TextIO.print "accepted\n"
    else TextIO.print "rejected\n"
  end;
End

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition compute_bounded_case10173_packed_batch_prog_def:
  compute_bounded_case10173_packed_batch_prog = ^prog
End

val _ = export_theory ();
