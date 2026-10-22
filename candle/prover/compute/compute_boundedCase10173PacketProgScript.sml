(*****************************************************************************
 * Direct CakeML program for the canonical genuine case-10173 packet.
 *
 * This extends the already translated complete historical checker.  It adds
 * the production packet decoder and executes that decoder plus every guard,
 * certificate check, center/box calculation, and final Taylor verdict.
 *****************************************************************************)
Theory compute_boundedCase10173PacketProg
Ancestors
  compute_boundedCase10173HistoricalCell0Prog
  compute_boundedCase10173Packet
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends "compute_boundedCase10173HistoricalCell0Prog";

val _ = register_type ``:bounded_case10173_packet``;

val _ = translate bounded_cv_encode_word64_def;
val _ = translate
  (bounded_cv_decode_word64_def
   |> REWRITE_RULE [compute_boundedTheory.bounded_word_base_eq]);
val _ = translate bounded_cv_encode_bool_def;
val _ = translate bounded_cv_decode_bool_def;
val _ = translate bounded_cv_encode_signed64_def;
val _ = translate
  (bounded_cv_decode_signed64_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate bounded_cv_encode_interval64_def;
val _ = translate
  (bounded_cv_decode_interval64_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate bounded_cv_encode_word64_list_def;

Theorem bounded_cv_tail_induction[local]:
  !P. (!v:cv. (!x y. v = Pair x y ==> P y) ==> P v) ==> !v. P v
Proof
  gen_tac
  >> strip_tac
  >> qspec_then `P` irule compute_execTheory.cv_induction
  >> rw []
  >> first_x_assum irule
  >> rw []
QED

val _ = translate_no_ind
  (bounded_cv_decode_word64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_decode_word64_list_ind[local]:
  bounded_cv_decode_word64_list_ind
Proof
  once_rewrite_tac [fetch "-" "bounded_cv_decode_word64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_cv_decode_word64_list_ind |> update_precondition;

val _ = translate bounded_cv_encode_interval64_list_def;
val _ = translate_no_ind
  (bounded_cv_decode_interval64_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_decode_interval64_list_ind[local]:
  bounded_cv_decode_interval64_list_ind
Proof
  once_rewrite_tac [fetch "-" "bounded_cv_decode_interval64_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_cv_decode_interval64_list_ind |> update_precondition;

val _ = translate bounded_cv_encode_sqrt64_certificate_def;
val _ = translate
  (bounded_cv_decode_sqrt64_certificate_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate bounded_cv_encode_sqrt64_certificate_list_def;
val _ = translate_no_ind
  (bounded_cv_decode_sqrt64_certificate_list_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);

Theorem bounded_cv_decode_sqrt64_certificate_list_ind[local]:
  bounded_cv_decode_sqrt64_certificate_list_ind
Proof
  once_rewrite_tac
    [fetch "-" "bounded_cv_decode_sqrt64_certificate_list_ind_def"]
  >> ACCEPT_TAC bounded_cv_tail_induction
QED

val _ = bounded_cv_decode_sqrt64_certificate_list_ind
  |> update_precondition;

val _ = translate bounded_case10173_packet_well_shaped_def;
val _ = translate bounded_cv_encode_case10173_packet_def;
val _ = translate
  (bounded_cv_decode_case10173_packet_def
   |> REWRITE_RULE [GSYM mloptionTheory.mapPartial_def]);
val _ = translate bounded_case10173_packet_accepts_def;
val _ = translate bounded_case10173_packet_check_cv_def;
val _ = translate bounded_case10173_cell0_packet_def;

Definition bounded_case10173_cell0_packet_program_check_def:
  bounded_case10173_cell0_packet_program_check () =
    (bounded_case10173_packet_check_cv
       (bounded_cv_encode_case10173_packet bounded_case10173_cell0_packet) =
     SOME (Num 1))
End

Theorem bounded_case10173_cell0_packet_program_check_value:
  bounded_case10173_cell0_packet_program_check ()
Proof
  simp [bounded_case10173_cell0_packet_program_check_def,
        bounded_case10173_cell0_packet_check_cv]
QED

val _ = translate bounded_case10173_cell0_packet_program_check_def;

Quote main = cakeml:
  if bounded_case10173_cell0_packet_program_check ()
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

Definition compute_bounded_case10173_packet_prog_def:
  compute_bounded_case10173_packet_prog = ^prog
End

val _ = export_theory ();
