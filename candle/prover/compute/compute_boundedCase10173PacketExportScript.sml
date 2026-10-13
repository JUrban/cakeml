(* Development export of the proved canonical-packet checker for direct cake. *)
Theory compute_boundedCase10173PacketExport
Ancestors
  compute_boundedCase10173PacketProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedCase10173PacketProgTheory.compute_bounded_case10173_packet_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_packet.sexp" prog;

val _ = export_theory ();
