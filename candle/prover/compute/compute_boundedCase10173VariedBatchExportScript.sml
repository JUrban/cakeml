(* Development export of the proved varied packet-batch checker. *)
Theory compute_boundedCase10173VariedBatchExport
Ancestors
  compute_boundedCase10173VariedBatchProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedCase10173VariedBatchProgTheory.compute_bounded_case10173_varied_batch_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_varied_batch.sexp" prog;

val _ = export_theory ();
