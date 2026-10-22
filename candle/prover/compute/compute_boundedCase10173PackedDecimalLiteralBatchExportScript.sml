(* Development S-expression export for the source-shaped full batch. *)
Theory compute_boundedCase10173PackedDecimalLiteralBatchExport
Ancestors
  compute_boundedCase10173PackedDecimalLiteralBatchProg
Libs
  preamble astToSexprLib

val prog =
  rhs (concl
    compute_boundedCase10173PackedDecimalLiteralBatchProgTheory.compute_bounded_case10173_packed_decimal_literal_batch_prog_def);

val _ = astToSexprLib.write_ast_to_file
  "compute_bounded_case10173_packed_decimal_literal_batch.sexp"
  prog;

val _ = export_theory ();
