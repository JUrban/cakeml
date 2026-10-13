(*****************************************************************************
 * Development export of the proved production-kernel packet benchmark for
 * the executable CakeML compiler.  The serialized AST is generated evidence
 * and is intentionally not tracked in git.
 *****************************************************************************)
Theory compute_candleKernelCase10173PacketRepeatSexpr
Ancestors
  compute_candleKernelCase10173PacketRepeatProg
Libs
  preamble astToSexprLib

val prog = rhs
  (concl
    compute_candleKernelCase10173PacketRepeatProgTheory.compute_candle_kernel_case10173_packet_repeat_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_candle_kernel_case10173_packet_repeat.sexp" prog;

val _ = export_theory ();
