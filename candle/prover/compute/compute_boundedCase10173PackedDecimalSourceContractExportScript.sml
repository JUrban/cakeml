(* Development export of the complete source-contract decimal batch checker. *)
Theory compute_boundedCase10173PackedDecimalSourceContractExport
Ancestors
  compute_boundedCase10173PackedDecimalBatchProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedCase10173PackedDecimalBatchProgTheory.compute_bounded_case10173_packed_decimal_batch_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_packed_decimal_source_contract.sexp" prog;

val _ = export_theory ();
