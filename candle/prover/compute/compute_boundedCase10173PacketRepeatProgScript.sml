(*****************************************************************************
 * Repeated exact-packet benchmark.  The canonical encoded genuine packet is
 * shared, while every iteration pays decoding plus the complete cell check.
 *****************************************************************************)
Theory compute_boundedCase10173PacketRepeatProg
Ancestors
  compute_boundedCase10173PacketProg
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase10173PacketProg";

Definition bounded_case10173_packet_check_repeat_def:
  bounded_case10173_packet_check_repeat 0 payload = T /\
  bounded_case10173_packet_check_repeat (SUC n) payload =
    (bounded_case10173_packet_check_cv payload = SOME (Num 1) /\
     bounded_case10173_packet_check_repeat n payload)
End

Theorem bounded_case10173_packet_check_repeat_accepts:
  bounded_case10173_packet_check_cv payload = SOME (Num 1) ==>
  !n. bounded_case10173_packet_check_repeat n payload
Proof
  strip_tac
  >> Induct
  >> simp [bounded_case10173_packet_check_repeat_def]
QED

Theorem bounded_case10173_cell0_packet_check_repeat_4173:
  bounded_case10173_packet_check_repeat 4173
    (bounded_cv_encode_case10173_packet bounded_case10173_cell0_packet)
Proof
  irule bounded_case10173_packet_check_repeat_accepts
  >> simp
       [compute_boundedCase10173PacketTheory.bounded_case10173_cell0_packet_check_cv]
QED

val _ = translate bounded_case10173_packet_check_repeat_def;

Quote main = cakeml:
  if bounded_case10173_packet_check_repeat 4173
       (bounded_cv_encode_case10173_packet bounded_case10173_cell0_packet)
  then TextIO.print "accepted\n"
  else TextIO.print "rejected\n";
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

Definition compute_bounded_case10173_packet_repeat_prog_def:
  compute_bounded_case10173_packet_repeat_prog = ^prog
End

val _ = export_theory ();
