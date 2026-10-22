(*****************************************************************************
 * Direct CakeML discriminator for a genuinely varied case-10173 packet batch.
 *
 * This extends the translated single-packet checker and adds only the
 * canonical packet-list decoder, batch fold, and three hash-pinned genuine
 * packets.  It is a focused development benchmark, not release evidence.
 *****************************************************************************)
Theory compute_boundedCase10173VariedBatchProg
Ancestors
  compute_boundedCase10173PacketProg
  compute_boundedCase10173VariedData
Libs
  preamble ml_translatorLib ml_progLib basis

open compute_boundedCase10173PacketBatchTheory
     compute_boundedCase10173VariedDataTheory;

val _ = translation_extends "compute_boundedCase10173PacketProg";

val _ = translate bounded_cv_encode_case10173_packet_list_def;
val _ = translate_no_ind
  (bounded_cv_decode_case10173_packet_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_batch_tail_induction[local]:
  !P. (!v:cv. (!x y. v = Pair x y ==> P y) ==> P v) ==> !v. P v
Proof
  gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

Theorem bounded_cv_decode_case10173_packet_list_ind[local]:
  bounded_cv_decode_case10173_packet_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_cv_decode_case10173_packet_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_batch_tail_induction
QED

val _ = bounded_cv_decode_case10173_packet_list_ind
  |> update_precondition;

val _ = translate bounded_case10173_packet_batch_accepts_def;
val _ = translate bounded_case10173_packet_batch_check_cv_def;

val _ = translate bounded_case10173_varied_packet0_def;
val _ = translate bounded_case10173_varied_packet1_def;
val _ = translate bounded_case10173_varied_packet2_def;
val _ = translate bounded_case10173_varied_prefix3_def;

Definition bounded_case10173_varied_prefix3_program_check_def:
  bounded_case10173_varied_prefix3_program_check () =
    (bounded_case10173_packet_batch_check_cv
       (bounded_cv_encode_case10173_packet_list
         bounded_case10173_varied_prefix3) = SOME (Num 1))
End

Theorem bounded_case10173_varied_prefix3_program_check_value:
  bounded_case10173_varied_prefix3_program_check ()
Proof
  simp [bounded_case10173_varied_prefix3_program_check_def,
        compute_boundedCase10173VariedDataTheory.bounded_case10173_varied_prefix3_check_cv]
QED

val _ = translate bounded_case10173_varied_prefix3_program_check_def;

Quote main = cakeml:
  if bounded_case10173_varied_prefix3_program_check ()
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

Definition compute_bounded_case10173_varied_batch_prog_def:
  compute_bounded_case10173_varied_batch_prog = ^prog
End

val _ = export_theory ();
