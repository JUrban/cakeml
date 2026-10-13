(* Development export of the complete packed varied case-10173 checker. *)
Theory compute_boundedCase10173PackedBatchExport
Ancestors
  compute_boundedCase10173PackedBatchProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedCase10173PackedBatchProgTheory.compute_bounded_case10173_packed_batch_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_packed_batch.sexp" prog;

val _ = export_theory ();
