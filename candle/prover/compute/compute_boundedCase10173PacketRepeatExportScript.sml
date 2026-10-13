(* Development export of the proved repeated exact-packet checker. *)
Theory compute_boundedCase10173PacketRepeatExport
Ancestors
  compute_boundedCase10173PacketRepeatProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedCase10173PacketRepeatProgTheory.compute_bounded_case10173_packet_repeat_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_packet_repeat.sexp" prog;

val _ = export_theory ();
