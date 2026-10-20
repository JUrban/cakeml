(* CakeML translation of the development source-shaped full batch. *)
Theory compute_boundedCase10173PackedDecimalLiteralBatchProg
Ancestors
  compute_boundedCase10173LiteralSourceDecimalProg
  compute_boundedCase10173PackedDecimalLiteralBatch
Libs
  preamble ml_translatorLib ml_progLib basis

val _ = translation_extends
  "compute_boundedCase10173LiteralSourceDecimalProg";

val _ = translate bounded_packed_chars_case10173_decimal_literal_packets_def;
val _ = translate bounded_packed_chars_case10173_decimal_literal_full_check_def;

Quote main = cakeml:
  let
    val payload = TextIO.inputAll (TextIO.openStdIn ())
  in
    if bounded_packed_chars_case10173_decimal_literal_full_check
         (String.explode payload)
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

Definition compute_bounded_case10173_packed_decimal_literal_batch_prog_def:
  compute_bounded_case10173_packed_decimal_literal_batch_prog = ^prog
End

val _ = export_theory ();
