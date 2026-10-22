(*****************************************************************************
 * Matched execution harness for the case-10173 fast evaluator installed in
 * the production Candle kernel.
 *
 * Unlike the standalone packet benchmark, this theory extends the actual
 * candle_kernelProg translator state and calls the exported Kernel values.
 * The HOL wrapper and its repeated acceptance theorem keep the benchmark
 * workload tied to the proved production evaluator rather than a copied
 * implementation.
 *****************************************************************************)
Theory compute_candleKernelCase10173PacketRepeatProg
Ancestors
  candle_kernelProg
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib basis

val _ = m_translation_extends "candle_kernelProg";

Definition candle_kernel_case10173_packet_check_def:
  candle_kernel_case10173_packet_check () =
    (registered_case10173_cell0_packet_fast_eval
       registered_case10173_cell0_ceqs
       registered_case10173_cell0_cexp =
     SOME registered_case10173_cell0_result)
End

Theorem candle_kernel_case10173_packet_check_value:
  candle_kernel_case10173_packet_check ()
Proof
  simp [candle_kernel_case10173_packet_check_def,
        compute_registeredCase10173PacketFastTheory.registered_case10173_cell0_packet_fast_eval_hit]
QED

Definition candle_kernel_case10173_packet_check_repeat_def:
  candle_kernel_case10173_packet_check_repeat 0 = T /\
  candle_kernel_case10173_packet_check_repeat (SUC n) =
    (candle_kernel_case10173_packet_check () /\
     candle_kernel_case10173_packet_check_repeat n)
End

Theorem candle_kernel_case10173_packet_check_repeat_value:
  !n. candle_kernel_case10173_packet_check_repeat n
Proof
  Induct
  >> simp [candle_kernel_case10173_packet_check_repeat_def,
           candle_kernel_case10173_packet_check_value]
QED

val _ = translate candle_kernel_case10173_packet_check_def;
val _ = translate candle_kernel_case10173_packet_check_repeat_def;

Quote main = cakeml:
  if candle_kernel_case10173_packet_check_repeat 4173
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

Definition compute_candle_kernel_case10173_packet_repeat_prog_def:
  compute_candle_kernel_case10173_packet_repeat_prog = ^prog
End

val _ = export_theory ();
